/*
** ARM64 instruction emitter.
** Copyright (C) 2005-2016 Mike Pall. See Copyright Notice in luajit.h
*/

/* -- Constant encoding --------------------------------------------------- */

/* Encode constant in K12 format for data processing instructions. */
static uint32_t emit_isk12(int64_t n)
{
  uint64_t k = (n < 0) ? -n : n;
  uint32_t m = (n < 0) ? 0x40000000 : 0;
  if (k < 4096) {
    return A64I_K12|m|A64F_U12(k);
  } else if ((k & 0xfff000) == k) {
    return A64I_K12|m|0x400000|A64F_U12(k>>12);
  }
  return 0;
}

#define emit_clz(n)	__builtin_clzll(n)
#define emit_ctz(n)	__builtin_ctzll(n)

/* Encode constant in K13 format for logical data processing instructions. */
static uint32_t emit_isk13(uint64_t n, int is64)
{
  int inv = 0, w = 64, s = 0xfff, xa, xb, res;
  uint64_t m = 1ULL, a, b, c;
  if (n & 1) {
    n = ~n;
    inv = 1;
  }
  if (!is64) {
    n <<= 32;
    n |= n >> 32;
  }
  a = n & -n;
  b = (n + a) & -(n + a);
  c = (n + a - b) & -(n + a - b);
  xa = 63 - emit_clz(a);
  xb = 63 - emit_clz(b);
  if (c) {
    w = 63 - emit_clz(c) - xa;
    if (w == 32) m = 0x0000000100000001UL;
    else if (w == 16) m = 0x0001000100010001UL;
    else if (w == 8) m = 0x0101010101010101UL;
    else if (w == 4) m = 0x1111111111111111UL;
    else if (w == 2) m = 0x5555555555555555UL;
    else return 0;
    s = (-2*w & 0x3f) - 1;
  } else if (!a) {
    return 0;
  } else if (xb == -1) {
    xb = 64;
  }
  if ((b-a) * m != n) return 0;
  if (inv) {
    res = ((w - xb) << 6) | (s+w+xa-xb);
  } else {
    res = ((w - xa) << 6) | (s+xb-xa);
  }
  return A64I_K13|(res << 10);
}

/* -- Emit basic instructions --------------------------------------------- */

static void emit_dnm(ASMState *as, A64Ins ai, Reg rd, Reg rn, Reg rm)
{
  *--as->mcp = ai | A64F_D(rd) | A64F_N(rn) | A64F_M(rm);
}

static void emit_dm(ASMState *as, A64Ins ai, Reg rd, Reg rm)
{
  *--as->mcp = ai | A64F_D(rd) | A64F_M(rm);
}

static void emit_dn(ASMState *as, A64Ins ai, Reg rd, Reg rn)
{
  *--as->mcp = ai | A64F_D(rd) | A64F_N(rn);
}

static void emit_nm(ASMState *as, A64Ins ai, Reg rn, Reg rm)
{
  *--as->mcp = ai | A64F_N(rn) | A64F_M(rm);
}

static void emit_d(ASMState *as, A64Ins ai, Reg rd)
{
  *--as->mcp = ai | A64F_D(rd);
}

static void emit_n(ASMState *as, A64Ins ai, Reg rn)
{
  *--as->mcp = ai | A64F_N(rn);
}

static int emit_checkofs(A64Ins ai, int64_t ofs)
{
  int scale = (ai >> 30) & 3;
  if (ofs < 0 || (ofs & ((1<<scale)-1))) {
    return (ofs >= -256 && ofs <= 255) ? -1 : 0;
  } else {
    return (ofs < (4096<<scale)) ? 1 : 0;
  }
}

static void emit_lso(ASMState *as, A64Ins ai, Reg rd, Reg rn, int64_t ofs)
{
  int ot = emit_checkofs(ai, ofs), sc = (ai >> 30) & 3, ofs2 = ofs - (1<<sc);
  uint32_t prev = *as->mcp & ~A64F_D(31);
  lua_assert(ot);
  if ((sc == 2 || sc == 3) && (ofs2 >= -64<<sc && ofs2 <= 63<<sc) &&
      (prev == (ai|A64F_N(rn)|A64F_U12(ofs2>>sc)) ||
       prev == ((ai^A64I_LS_U)|A64F_N(rn)|A64F_S9(ofs2&0x1ff))) &&
      ((ai & 0x400000) ? rd != rn : 1) && (as->mcp != as->mcloop)) {
    *as->mcp = (ai == A64I_LDRx ? A64I_LDPx :
		ai == A64I_LDRw ? A64I_LDPw :
		ai == A64I_LDRd ? A64I_LDPd :
		ai == A64I_LDRs ? A64I_LDPs :
		ai == A64I_STRx ? A64I_STPx :
		ai == A64I_STRw ? A64I_STPw :
		ai == A64I_STRd ? A64I_STPd : A64I_STPs) | A64F_A(rd) |
	       A64F_D(*as->mcp & 31) | A64F_N(rn) | ((ofs2 >> sc) << 15);
    return;
  }
  if (ot == 1)
    *--as->mcp = ai | A64F_D(rd) | A64F_N(rn) | A64F_U12(ofs >> sc);
  else
    *--as->mcp = (ai^A64I_LS_U) | A64F_D(rd) | A64F_N(rn) | A64F_S9(ofs & 0x1ff);
}

/* -- Emit loads/stores --------------------------------------------------- */

/* Prefer spills of BASE/L. */
#define emit_canremat(ref)	((ref) <= ASMREF_L)

/* Load a 32 bit constant into a GPR. */
#define emit_loadi(as, rd, i)	emit_loadk(as, rd, i, 0)

/* Load a 64 bit constant into a GPR. */
#define emit_loadu64(as, rd, i)	emit_loadk(as, rd, i, 1)

#define emit_loada(as, r, addr)	emit_loadu64(as, (r), (uintptr_t)(addr))

static void emit_loadk(ASMState *as, Reg rd, uint64_t u64, int is64)
{
  int i, neg, ones = 0, zeros = 0, shift = 0, lshift = 0;
  uint32_t k13 = emit_isk13(u64, is64);
  uint64_t frag[4], n64;
  /* Can the constant be represented as a bitmask immediate? */
  if(k13) {
    emit_dn(as, (is64 ? A64I_ORRx : A64I_ORRw)^k13, rd, RID_ZERO);
    return;
  }
  if (!is64) u64 = (int64_t)(int32_t)u64;
  /* Count homogenous 16-bit fragments. */
  for (i = 0; i < 4; i++) {
    frag[i] = (u64>>i*16) & 0xffff;
    if (frag[i] == 0xffff) ones++;
    else if (frag[i] == 0) zeros++;
  }
  /* Try to emit ORR+MOVK. Applies to constants with AXBX or XAXB pattern. */
  if (is64 && ones < 3 && zeros < 3) {
    for (i = 0; i < 2; i++) {
      if (frag[i] == frag[i+2]) {
	int j, a = i+1, b = (i+3)%4;
	for (j = 0; j < 2; j++) {
	  k13 = emit_isk13((u64 & ~(0xffffull<<16*b)) | (frag[a]<<16*b), 1);
	  if (k13) {
	    emit_d(as, A64I_MOVKx | A64F_U16(frag[b]) | A64F_LSL16(16*b), rd);
	    emit_dn(as, A64I_ORRx^k13, rd, RID_ZERO);
	    return;
	  }
	  a = b; b = i+1;
	}
      }
    }
  }
  /* Use MOVN if it pays off. */
  neg = ones > zeros;
  n64 = neg ? ~u64 : u64;
  /* Find first/last fragment to be filled. */
  if (n64 != 0) {
    shift = ((63-emit_clz(n64))/16)*16;
    lshift = (emit_ctz(n64)/16)*16;
  }
  /* MOVK requires the original value (u64). */
  while (shift > lshift) {
    uint32_t u16 = (u64 >> shift) & 0xffff;
    /* Skip fragments that are correctly filled by MOVN/MOVZ. */
    if (u16 != (neg ? 0xffff : 0))
      emit_d(as, (is64 ? A64I_MOVKx : A64I_MOVKw) | A64F_U16(u16) |
		 A64F_LSL16(shift), rd);
    shift -= 16;
  }
  /* But MOVN needs an inverted value (n64). */
  emit_d(as, (neg ? A64I_MOVNx : A64I_MOVZx) |
	     A64F_U16((n64 >> lshift) & 0xffff) | A64F_LSL16(lshift), rd);
}

#define glofs(as, k) \
  ((intptr_t)((uintptr_t)(k) - (uintptr_t)&J2GG(as->J)->g))
#define mcpofs(as, k) \
  ((intptr_t)((uintptr_t)(k) - (uintptr_t)as->mcp))
#define checkmcpofs(as, k) \
  ((((mcpofs(as, k)>>2) + 0x00040000) >> 19) == 0)

static Reg ra_allock(ASMState *as, intptr_t k, RegSet allow);

/* Get/set from constant pointer. */
static void emit_lsptr(ASMState *as, A64Ins ai, Reg r, void *p)
{
  if (!(ai & 0x00400000) || !checkmcpofs(as, p)) {
    int64_t ofs = glofs(as, p);
    Reg base;
    if (emit_checkofs(ai, ofs)) {
      base = RID_GL;
    } else {
      int64_t i = i64ptr(p);
      base = ra_allock(as, (i & ~0x7fffull), rset_exclude(RSET_GPR, r));
      ofs = i & 0x7fffull;
    }
    emit_lso(as, ai, r, base, ofs);
  } else {
    emit_d(as, A64I_LDRLx | A64F_S19(mcpofs(as, p)>>2), r);
  }
}

/* Load 64 bit IR constant into register. */
static void emit_loadk64(ASMState *as, Reg r, IRIns *ir)
{
  const uint64_t *k = &ir_k64(ir)->u64;
  Reg r64 = r;
  if (rset_test(RSET_FPR, r)) {
    r64 = RID_TMP;
    emit_dn(as, A64I_FMOV_D_R, (r & 31), r64);
  }
  if (emit_checkofs(A64I_LDRx, glofs(as, k)) || checkmcpofs(as, k))
    emit_lsptr(as, A64I_LDRx, r64, (void *)k);
  else
    emit_loadu64(as, r64, *k);
}

/* Get/set global_State fields. */
#define emit_getgl(as, r, field) \
  emit_lsptr(as, A64I_LDRx, (r), (void *)&J2G(as->J)->field)
#define emit_setgl(as, r, field) \
  emit_lsptr(as, A64I_STRx, (r), (void *)&J2G(as->J)->field)

/* Trace number is determined from pc of exit instruction. */
#define emit_setvmstate(as, i)	UNUSED(i)

/* -- Emit control-flow instructions -------------------------------------- */

/* Label for internal jumps. */
typedef MCode *MCLabel;

/* Return label pointing to current PC. */
#define emit_label(as)		((as)->mcp)

static void emit_cond_branch(ASMState *as, A64CC cond, MCode *target)
{
  MCode *p = as->mcp;
  ptrdiff_t delta = target - (p - 1);
  lua_assert(((delta + 0x40000) >> 19) == 0);
  *--p = A64I_BCC | A64F_S19((uint32_t)delta & 0x7ffff) | cond;
  as->mcp = p;
}

static void emit_branch(ASMState *as, A64Ins ai, MCode *target)
{
  MCode *p = as->mcp;
  ptrdiff_t delta = target - (p - 1);
  lua_assert(((delta + 0x02000000) >> 26) == 0);
  *--p = ai | ((uint32_t)delta & 0x03ffffffu);
  as->mcp = p;
}

#define emit_jmp(as, target)	emit_branch(as, A64I_B, (target))

static void emit_call(ASMState *as, void *target)
{
  MCode *p = --as->mcp;
  ptrdiff_t delta = (char *)target - (char *)p;
  if ((((delta>>2) + 0x02000000) >> 26) == 0) {
    *p = A64I_BL | ((uint32_t)(delta>>2) & 0x03ffffffu);
  } else {  /* Target out of range: need indirect call. But don't use R0-R7. */
    Reg r = ra_allock(as, i64ptr(target),
		      RSET_RANGE(RID_X8, RID_MAX_GPR)-RSET_FIXED);
    *p = A64I_BLR | A64F_N(r);
  }
}

/* -- Emit generic operations --------------------------------------------- */

/* Generic move between two regs. */
static void emit_movrr(ASMState *as, IRIns *ir, Reg dst, Reg src)
{
  if (dst >= RID_MAX_GPR) {
    emit_dn(as, irt_isnum(ir->t) ? A64I_FMOV_D : A64I_FMOV_S,
	    (dst & 31), (src & 31));
    return;
  }
  if (as->mcp != as->mcloop) {  /* Swap early registers for loads/stores. */
    MCode ins = *as->mcp, swp = (src^dst);
    if ((ins & 0xbf800000) == 0xb9000000) {
      if (!((ins ^ (dst << 5)) & 0x000003e0))
	*as->mcp = ins ^ (swp << 5);  /* Swap N in load/store. */
      if (!(ins & 0x00400000) && !((ins ^ dst) & 0x0000001f))
	*as->mcp = ins ^ swp;  /* Swap D in store. */
    }
  }
  emit_dm(as, A64I_MOVx, dst, src);
}

/* Generic load of register with base and (small) offset address. */
static void emit_loadofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  if (r >= RID_MAX_GPR)
    emit_lso(as, irt_isnum(ir->t) ? A64I_LDRd : A64I_LDRs, (r & 31), base, ofs);
  else
    emit_lso(as, irt_is64(ir->t) ? A64I_LDRx : A64I_LDRw, r, base, ofs);
}

/* Generic store of register with base and (small) offset address. */
static void emit_storeofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  if (r >= RID_MAX_GPR)
    emit_lso(as, irt_isnum(ir->t) ? A64I_STRd : A64I_STRs, (r & 31), base, ofs);
  else
    emit_lso(as, irt_is64(ir->t) ? A64I_STRx : A64I_STRw, r, base, ofs);
}

/* Emit an arithmetic operation with a constant operand. */
static void emit_opk(ASMState *as, A64Ins ai, Reg dest, Reg src,
		     int32_t i, RegSet allow)
{
  uint32_t k = emit_isk12(i);
  if (k)
    emit_dn(as, ai^k, dest, src);
  else
    emit_dnm(as, ai, dest, src, ra_allock(as, i, allow));
}

/* Add offset to pointer. */
static void emit_addptr(ASMState *as, Reg r, int32_t ofs)
{
  if (ofs)
    emit_opk(as, ofs < 0 ? A64I_SUBx : A64I_ADDx, r, r,
	     ofs < 0 ? -ofs : ofs, rset_exclude(RSET_GPR, r));
}

#define emit_spsub(as, ofs)	emit_addptr(as, RID_SP, -(ofs))

