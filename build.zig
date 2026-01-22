// Working builds:
// zig build -Dtarget=x86-windows
// zig build -Dtarget=x86_64-windows
// zig build -Dtarget=aarch64-windows
// zig build -Dtarget=x86-linux-musl
// zig build -Dtarget=x86_64-linux-musl
// zig build -Dtarget=arm-linux-musleabihf
// zig build -Dtarget=arm-linux-musleabi
// zig build -Dtarget=aarch64-linux-musl
// zig build -Dtarget=aarch64_be-linux-musl
// zig build -Dtarget=powerpc-linux-musleabi
// zig build -Dtarget=powerpc-linux-musleabihf
// zig build -Dtarget=mips-linux-musleabi
// zig build -Dtarget=mips-linux-musleabihf
// zig build -Dtarget=mipsel-linux-musleabi
// zig build -Dtarget=mipsel-linux-musleabihf
// zig build -Dtarget=mips64-linux-muslabi64
// zig build -Dtarget=mips64el-linux-muslabi64

// TODO: It is unclear how to invoke MIPS64 soft-float build.
//       mips64-linux-musleabi/gnueabi does not work.

const std = @import("std");

var alloc: std.mem.Allocator = undefined;
var target_defines: []const u8 = undefined;
var host_flags: std.ArrayList([]const u8) = .empty;
var dasm_flags: std.ArrayList([]const u8) = .empty;
var cflags: std.ArrayList([]const u8) = .empty;

pub fn build(b: *std.Build) !void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    alloc = b.allocator;

    const arch = target.result.cpu.arch;
    const target_sys = target.result.os.tag;
    const host_sys = b.graph.host.result.os.tag;

    populateTargetDefines(getTriple(target.result));

    const target_ljarch = getTargetLjarch();
    const dasm_arch = if (std.mem.eql(u8, target_ljarch, "x64") and !defineEquals("LJ_FR2", "1")) "x86" else target_ljarch;

    // Set up DASM flags.
    addDasmFlagC("-D", "ENDIAN_LE", defineEquals("LJ_LE", "1"));
    addDasmFlagC("-D", "ENDIAN_BE", defineEquals("LJ_BE", "1"));
    addDasmFlagC("-D", "P64", defineEquals("LJ_ARCH_BITS", "64"));
    addDasmFlagC("-D", "JIT", defineEquals("LJ_HASJIT", "1"));
    addDasmFlagC("-D", "FFI", defineEquals("LJ_HASFFI", "1"));
    addDasmFlagC("-D", "DUALNUM", defineEquals("LJ_DUALNUM", "1"));
    addDasmFlagC("-D", "FPU", defineEquals("LJ_ARCH_HASFPU", "1"));
    addDasmFlagC("-D", "HFABI", !defineEquals("LJ_ABI_SOFTFP", "1"));
    addDasmFlagC("-D", "WIN", target_sys == .windows);
    addDasmFlagC("-D", "NO_UNWIND", defineEquals("LJ_NO_UNWIND", "1"));
    addDasmFlagC("-D", "PAUTH", defineEquals("LJ_ABI_PAUTH", "1"));
    addDasmFlagC("-D", "IOS", std.mem.eql(u8, target_ljarch, "arm") and target_sys == .ios);
    addDasmFlagC("-D", "MIPSR6", hasDefine("LJ_TARGET_MIPSR6"));

    const is_ppc = std.mem.eql(u8, target_ljarch, "ppc");
    addDasmFlagC("-D", "SQRT", is_ppc and defineEquals("LJ_ARCH_SQRT", "1"));
    addDasmFlagC("-D", "ROUND", is_ppc and defineEquals("LJ_ARCH_ROUND", "1"));
    addDasmFlagC("-D", "GPR64", is_ppc and defineEquals("LJ_ARCH_PPC32ON64", "1"));
    addDasmFlagC("-D", "PPE", is_ppc and target_sys == .ps3);
    addDasmFlagC("-D", "TOC", is_ppc and target_sys == .ps3);

    const minilua = b.addExecutable(.{
        .name = "minilua",
        .root_module = b.createModule(.{
            .target = b.graph.host, // This is always executed on the host system!
            .optimize = std.builtin.OptimizeMode.ReleaseFast, // TODO: Does not work in Debug.
            .link_libc = true,
        }),
    });
    minilua.root_module.addCSourceFile(.{ .file = b.path("src/host/minilua.c") });

    const gen_buildvm_arch = b.addRunArtifact(minilua);
    gen_buildvm_arch.addFileArg(b.path("dynasm/dynasm.lua"));
    gen_buildvm_arch.addArgs(dasm_flags.items);
    gen_buildvm_arch.addArg("-o");
    const buildvm_arch = gen_buildvm_arch.addOutputFileArg("generated/buildvm_arch.h");
    const dasc_file = join3("src/vm_", dasm_arch, ".dasc");
    gen_buildvm_arch.addFileArg(b.path(dasc_file));

    const gen_relver = b.addSystemCommand(&.{ "git", "show", "-s", "--format=%ct", "--output" });
    const relver = gen_relver.addOutputFileArg("generated/luajit_relver.txt");

    const gen_version = b.addRunArtifact(minilua);
    gen_version.addFileArg(b.path("src/host/genversion.lua"));
    gen_version.addFileArg(b.path("src/luajit_rolling.h"));
    gen_version.addFileArg(relver);
    const luajith = gen_version.addOutputFileArg("generated/luajit.h");
    gen_version.step.dependOn(&gen_relver.step);

    // Set up HOST flags.
    addHostFlagC("-D__AARCH64EB__=1", hasDefine("LJ_TARGET_ARM64") and hasDefine("__AARCH64EB__"));
    addHostFlagC("-DLJ_ARCH_ENDIAN=LUAJIT_LE", hasDefine("LJ_TARGET_PPC") and defineEquals("LJ_LE", "1"));
    addHostFlagC("-DLJ_ARCH_ENDIAN=LUAJIT_BE", hasDefine("LJ_TARGET_PPC") and defineEquals("LJ_BE", "1"));
    addHostFlagC("-D__MIPSEL__=1", hasDefine("LJ_TARGET_MIPS") and hasDefine("MIPSEL"));
    addHostFlagC("-D__CELLOS_LV2__", defineEquals("LJ_TARGET_PS3", "1"));
    addHostFlagC("-DLJ_ARCH_HASFPU=1", defineEquals("LJ_ARCH_HASFPU", "1"));
    addHostFlagC("-DLJ_ARCH_HASFPU=0", !defineEquals("LJ_ARCH_HASFPU", "1"));
    addHostFlagC("-DLJ_ABI_SOFTFP=1", defineEquals("LJ_ABI_SOFTFP", "1"));
    addHostFlagC("-DLJ_ABI_SOFTFP=0", !defineEquals("LJ_ABI_SOFTFP", "1"));
    addHostFlagC("-DLUAJIT_NO_UNWIND", defineEquals("LJ_NO_UNWIND", "1"));
    addHostFlagC("-DLJ_ABI_PAUTH=1", defineEquals("LJ_ABI_PAUTH", "1"));
    addHostFlag(join2("-DLUAJIT_TARGET=LUAJIT_ARCH_", target_ljarch));

    // WORKAROUND: LLVM assembler cannot handle writable EH frames.
    addHostFlagC("-DLJ_NO_UNWIND=1", arch.isMIPS32());

    // WORKAROUND: Windows paths in #line cause errors.
    addHostFlagC("-Wno-unknown-escape-sequence", target_sys == .windows);

    if (host_sys != target_sys) {
        // TODO: This is probably not the same as what Makefile does.
        switch (target_sys) {
            .windows => {
                addHostFlag("-malign-double");
                addHostFlag("-DLUAJIT_OS=LUAJIT_OS_WINDOWS");
            },
            .linux => {
                addHostFlag("-DLUAJIT_OS=LUAJIT_OS_LINUX");
            },
            .macos => {
                addHostFlag("-DLUAJIT_OS=LUAJIT_OS_OSX");
            },
            .ios => {
                addHostFlag("-DLUAJIT_OS=LUAJIT_OS_OSX");
                addHostFlag("-DTARGET_OS_IPHONE=1");
            },
            else => {
                addHostFlag("-DLUAJIT_OS=LUAJIT_OS_OTHER");
            },
        }
    }

    const buildvm = b.addExecutable(.{
        .name = "buildvm",
        .root_module = b.createModule(.{
            // This is always executed on the host system. If the target system
            // is 32-bit and the host system is 64-bit, buildvm needs to be
            // compiled in 32-bit mode.
            //
            // TODO: This should work for other architectures, not just x86_64.
            .target = if (target.result.ptrBitWidth() == 32 and b.graph.host.result.ptrBitWidth() == 64) b.resolveTargetQuery(.{
                .cpu_arch = .x86,
                .os_tag = b.graph.host.result.os.tag,
                .abi = b.graph.host.result.abi,
            }) else b.graph.host,
            .optimize = std.builtin.OptimizeMode.ReleaseFast, // TODO: Does not work in Debug.
            .link_libc = true,
        }),
    });
    const buildvm_sources = [_][]const u8{
        "src/host/buildvm.c",
        "src/host/buildvm_asm.c",
        "src/host/buildvm_peobj.c",
        "src/host/buildvm_lib.c",
        "src/host/buildvm_fold.c",
    };

    for (buildvm_sources) |f| buildvm.root_module.addCSourceFile(.{ .file = b.path(f), .flags = host_flags.items });
    buildvm.root_module.addIncludePath(b.path("src"));
    buildvm.root_module.addIncludePath(b.path("src/host"));
    buildvm.root_module.addIncludePath(buildvm_arch.dirname());
    buildvm.root_module.addIncludePath(luajith.dirname());
    buildvm.step.dependOn(&gen_buildvm_arch.step);
    buildvm.step.dependOn(&gen_version.step);

    const gen_folddef = b.addRunArtifact(buildvm);
    gen_folddef.addArgs(&.{ "-m", "folddef", "-o" });
    const folddef = gen_folddef.addOutputFileArg("generated/lj_folddef.h");
    gen_folddef.addFileArg(b.path("src/lj_opt_fold.c"));

    const gen_libdef = b.addRunArtifact(buildvm);
    gen_libdef.addArgs(&.{ "-m", "libdef", "-o" });
    const libdef = gen_libdef.addOutputFileArg("generated/lj_libdef.h");
    const all_libs = [_][]const u8{
        "src/lib_base.c",
        "src/lib_math.c",
        "src/lib_bit.c",
        "src/lib_string.c",
        "src/lib_table.c",
        "src/lib_io.c",
        "src/lib_os.c",
        "src/lib_package.c",
        "src/lib_debug.c",
        "src/lib_jit.c",
        "src/lib_ffi.c",
        "src/lib_buffer.c",
    };
    for (all_libs) |lib| gen_libdef.addFileArg(b.path(lib));

    const gen_ffdef = b.addRunArtifact(buildvm);
    gen_ffdef.addArgs(&.{ "-m", "ffdef", "-o" });
    const ffdef = gen_ffdef.addOutputFileArg("generated/lj_ffdef.h");
    for (all_libs) |lib| gen_ffdef.addFileArg(b.path(lib));

    const gen_bcdef = b.addRunArtifact(buildvm);
    gen_bcdef.addArgs(&.{ "-m", "bcdef", "-o" });
    const bcdef = gen_bcdef.addOutputFileArg("generated/lj_bcdef.h");
    for (all_libs) |lib| gen_bcdef.addFileArg(b.path(lib));

    const gen_recdef = b.addRunArtifact(buildvm);
    gen_recdef.addArgs(&.{ "-m", "recdef", "-o" });
    const recdef = gen_recdef.addOutputFileArg("generated/lj_recdef.h");
    for (all_libs) |lib| gen_recdef.addFileArg(b.path(lib));

    const ljvm_mode = switch (target_sys) {
        .windows => "peobj",
        .linux => "elfasm",
        .macos => "machasm",
        else => @panic("Unsupported operating system."),
    };

    const gen_ljvm = b.addRunArtifact(buildvm);
    gen_ljvm.addArgs(&.{ "-m", ljvm_mode, "-o" });
    const ljvm = gen_ljvm.addOutputFileArg(if (target_sys == .windows) "generated/lj_vm.obj" else "generated/lj_vm.S");

    addCFlag("-DLUAJIT_UNWIND_EXTERNAL");
    if (arch == .arm) {
        // WORKAROUND: Zig compiler runtime doesn't declare __float* and __fix* builtins.
        addCFlag("-D__floatdidf=__aeabi_l2d");
        addCFlag("-D__floatundidf=__aeabi_ul2d");
        addCFlag("-D__floatdisf=__aeabi_l2f");
        addCFlag("-D__floatundisf=__aeabi_ul2f");
        addCFlag("-D__fixdfdi=__aeabi_d2lz");
        addCFlag("-D__fixunsdfdi=__aeabi_d2ulz");
        addCFlag("-D__fixsfdi=__aeabi_f2lz");
        addCFlag("-D__fixunssfdi=__aeabi_f2ulz");
    }
    if (arch.isMIPS()) {
        // WORKAROUND: __clear_cache is not declared in any header.
        addCFlag("-Wno-error=implicit-function-declaration");
    }

    const libluajit = b.addLibrary(.{
        .name = "libluajit",
        .linkage = .static,
        .root_module = b.createModule(.{
            .optimize = optimize,
            .target = target,
            .link_libc = true,
        }),
    });
    const libluajit_sources = [_][]const u8{
        "src/lj_gc.c",
        "src/lj_err.c",
        "src/lj_char.c",
        "src/lj_bc.c",
        "src/lj_obj.c",
        "src/lj_buf.c",
        "src/lj_str.c",
        "src/lj_tab.c",
        "src/lj_func.c",
        "src/lj_udata.c",
        "src/lj_meta.c",
        "src/lj_debug.c",
        "src/lj_state.c",
        "src/lj_dispatch.c",
        "src/lj_vmevent.c",
        "src/lj_vmmath.c",
        "src/lj_serialize.c",
        "src/lj_strscan.c",
        "src/lj_strfmt.c",
        "src/lj_strfmt_num.c",
        "src/lj_api.c",
        "src/lj_profile.c",
        "src/lj_prng.c",
        "src/lj_lex.c",
        "src/lj_parse.c",
        "src/lj_bcread.c",
        "src/lj_bcwrite.c",
        "src/lj_load.c",
        "src/lj_ir.c",
        "src/lj_opt_mem.c",
        "src/lj_opt_fold.c",
        "src/lj_opt_narrow.c",
        "src/lj_opt_dce.c",
        "src/lj_opt_loop.c",
        "src/lj_opt_split.c",
        "src/lj_opt_sink.c",
        "src/lj_mcode.c",
        "src/lj_snap.c",
        "src/lj_record.c",
        "src/lj_crecord.c",
        "src/lj_ffrecord.c",
        "src/lj_asm.c",
        "src/lj_trace.c",
        "src/lj_gdbjit.c",
        "src/lj_ctype.c",
        "src/lj_cdata.c",
        "src/lj_cconv.c",
        "src/lj_ccall.c",
        "src/lj_ccallback.c",
        "src/lj_carith.c",
        "src/lj_clib.c",
        "src/lj_cparse.c",
        "src/lj_lib.c",
        "src/lj_alloc.c",
        "src/lib_aux.c",
        "src/lib_base.c",
        "src/lib_buffer.c",
        "src/lib_math.c",
        "src/lib_bit.c",
        "src/lib_string.c",
        "src/lib_table.c",
        "src/lib_io.c",
        "src/lib_os.c",
        "src/lib_package.c",
        "src/lib_debug.c",
        "src/lib_jit.c",
        "src/lib_ffi.c",
        "src/lib_init.c",
    };
    for (libluajit_sources) |f| libluajit.root_module.addCSourceFile(.{ .file = b.path(f), .flags = cflags.items });
    if (target_sys == .windows) {
        libluajit.root_module.addObjectFile(ljvm);
    } else {
        libluajit.root_module.addAssemblyFile(ljvm);
    }

    // This is a workaround for Zig not having __aeabi_cdcmp* implementations in compiler runtime.
    if (arch == .arm) {
        const wf = b.addWriteFiles();
        const cdcmp_src = wf.add("cdcmp.zig", cdcmp);
        const cdcmp_mod = b.createModule(.{
            .root_source_file = cdcmp_src,
            .target = target,
            .optimize = optimize,
        });

        const cdcmp_obj = b.addObject(.{
            .name = "zig_part",
            .root_module = cdcmp_mod,
        });
        libluajit.addObject(cdcmp_obj);
    }

    libluajit.root_module.addIncludePath(b.path("src"));
    libluajit.root_module.addIncludePath(b.path("src/host"));
    libluajit.root_module.addIncludePath(folddef.dirname());
    libluajit.root_module.addIncludePath(libdef.dirname());
    libluajit.root_module.addIncludePath(ffdef.dirname());
    libluajit.root_module.addIncludePath(bcdef.dirname());
    libluajit.root_module.addIncludePath(recdef.dirname());
    libluajit.root_module.addIncludePath(luajith.dirname());

    libluajit.step.dependOn(&gen_folddef.step);
    libluajit.step.dependOn(&gen_libdef.step);
    libluajit.step.dependOn(&gen_ffdef.step);
    libluajit.step.dependOn(&gen_bcdef.step);
    libluajit.step.dependOn(&gen_recdef.step);
    libluajit.step.dependOn(&gen_ljvm.step);
    libluajit.step.dependOn(&gen_version.step);

    const luajit = b.addExecutable(.{
        .name = "luajit",
        .root_module = b.createModule(.{
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
    });
    luajit.root_module.addCSourceFile(.{ .file = b.path("src/luajit.c"), .flags = cflags.items });
    luajit.root_module.addIncludePath(b.path("src"));
    luajit.root_module.addIncludePath(luajith.dirname());
    luajit.root_module.linkLibrary(libluajit);
    luajit.step.dependOn(&gen_version.step);

    if (target_sys == .linux) {
        luajit.root_module.linkSystemLibrary("unwind", .{});
    }

    b.installArtifact(luajit);
}

fn addCFlag(flag: []const u8) void {
    cflags.append(alloc, flag) catch unreachable;
}

fn addDasmFlagC(flag1: []const u8, flag2: []const u8, cond: bool) void {
    if (cond) {
        dasm_flags.append(alloc, flag1) catch unreachable;
        dasm_flags.append(alloc, flag2) catch unreachable;
    }
}

fn addHostFlag(flag: []const u8) void {
    host_flags.append(alloc, flag) catch unreachable;
}

fn addHostFlagC(flag: []const u8, cond: bool) void {
    if (cond)
        host_flags.append(alloc, flag) catch unreachable;
}

fn join2(s1: []const u8, s2: []const u8) []const u8 {
    return std.mem.concat(alloc, u8, &.{ s1, s2 }) catch unreachable;
}

fn join3(s1: []const u8, s2: []const u8, s3: []const u8) []const u8 {
    return std.mem.concat(alloc, u8, &.{ s1, s2, s3 }) catch unreachable;
}

fn getTriple(t: std.Target) []u8 {
    if (t.abi == .none)
        return std.fmt.allocPrint(alloc, "{s}-{s}", .{
            @tagName(t.cpu.arch),
            @tagName(t.os.tag),
        }) catch unreachable;
    return std.fmt.allocPrint(alloc, "{s}-{s}-{s}", .{
        @tagName(t.cpu.arch),
        @tagName(t.os.tag),
        @tagName(t.abi),
    }) catch unreachable;
}

fn populateTargetDefines(triple: []const u8) void {
    var argv: std.ArrayList([]const u8) = .empty;
    defer argv.deinit(alloc);
    argv.appendSlice(alloc, &.{
        "zig",
        "cc",
        "-E",
        "-dM",
        "-target",
        triple,
        "-D_FILE_OFFSET_BITS=64",
        "-D_LARGEFILE_SOURCE",
        "-U_FORTIFY_SOURCE",
        "src/lj_arch.h",
    }) catch unreachable;

    var child = std.process.Child.init(argv.items, alloc);
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;
    child.spawn() catch unreachable;

    const out = child.stdout.?.readToEndAlloc(alloc, 10 * 1024 * 1024) catch unreachable;
    const err = child.stderr.?.readToEndAlloc(alloc, 128 * 1024) catch unreachable;
    const term = child.wait() catch unreachable;

    switch (term) {
        .Exited => |code| if (code != 0) {
            std.debug.panic("preprocess failed ({d}): {s}\n", .{ code, err });
        },
        else => {
            std.debug.panic("preprocess failed: {s}\n", .{err});
        },
    }
    target_defines = out;
}

fn hasDefine(name: []const u8) bool {
    var lines = std.mem.tokenizeScalar(u8, target_defines, '\n');
    while (lines.next()) |line_raw| {
        const line = std.mem.trim(u8, line_raw, " \t\r");
        if (!std.mem.startsWith(u8, line, "#define ")) continue;
        var it = std.mem.tokenizeAny(u8, line[8..], " \t(");
        if (std.mem.eql(u8, it.next() orelse continue, name)) return true;
    }
    return false;
}

fn defineEquals(name: []const u8, value: []const u8) bool {
    var lines = std.mem.tokenizeScalar(u8, target_defines, '\n');
    while (lines.next()) |line_raw| {
        const line = std.mem.trim(u8, line_raw, " \t\r");
        if (!std.mem.startsWith(u8, line, "#define ")) continue;
        var it = std.mem.tokenizeAny(u8, line[8..], " \t(");
        const n = it.next() orelse continue;
        if (!std.mem.eql(u8, n, name)) continue;
        const v = it.next() orelse "1";
        return std.mem.eql(u8, v, value);
    }
    return false;
}

fn getTargetLjarch() []const u8 {
    if (hasDefine("LJ_TARGET_X64")) {
        return "x64";
    } else if (hasDefine("LJ_TARGET_X86")) {
        return "x86";
    } else if (hasDefine("LJ_TARGET_ARM")) {
        return "arm";
    } else if (hasDefine("LJ_TARGET_ARM64")) {
        return "arm64";
    } else if (hasDefine("LJ_TARGET_PPC")) {
        return "ppc";
    } else if (hasDefine("LJ_TARGET_MIPS")) {
        if (hasDefine("LJ_TARGET_MIPS64")) {
            return "mips64";
        } else {
            return "mips";
        }
    } else if (hasDefine("LJ_TARGET_PPC")) {
        return "ppc";
    } else {
        @panic("Unsupported architecture.");
    }
}

// Implementation of __aeabi_cdcmple and __aeabi_cdcmpeq, required for ARM build.
const cdcmp =
    \\ const std = @import("std");
    \\
    \\ const LE = enum(i32) {
    \\     Less = -1,
    \\     Equal = 0,
    \\     Greater = 1,
    \\
    \\     const Unordered: LE = .Greater;
    \\ };
    \\
    \\ fn cmpf2(comptime T: type, comptime RT: type, a: T, b: T) RT {
    \\     const bits = @typeInfo(T).float.bits;
    \\     const srep_t = std.meta.Int(.signed, bits);
    \\     const rep_t = std.meta.Int(.unsigned, bits);
    \\
    \\     const significandBits = std.math.floatMantissaBits(T);
    \\     const exponentBits = std.math.floatExponentBits(T);
    \\     const signBit = (@as(rep_t, 1) << (significandBits + exponentBits));
    \\     const absMask = signBit - 1;
    \\     const infT = comptime std.math.inf(T);
    \\     const infRep = @as(rep_t, @bitCast(infT));
    \\
    \\     const aInt = @as(srep_t, @bitCast(a));
    \\     const bInt = @as(srep_t, @bitCast(b));
    \\     const aAbs = @as(rep_t, @bitCast(aInt)) & absMask;
    \\     const bAbs = @as(rep_t, @bitCast(bInt)) & absMask;
    \\
    \\     // If either a or b is NaN, they are unordered.
    \\     if (aAbs > infRep or bAbs > infRep) return RT.Unordered;
    \\
    \\     // If a and b are both zeros, they are equal.
    \\     if ((aAbs | bAbs) == 0) return .Equal;
    \\
    \\     // If at least one of a and b is positive, we get the same result comparing
    \\     // a and b as signed integers as we would with a floating-point compare.
    \\     if ((aInt & bInt) >= 0) {
    \\         if (aInt < bInt) {
    \\             return .Less;
    \\         } else if (aInt == bInt) {
    \\             return .Equal;
    \\         } else return .Greater;
    \\     } else {
    \\         // Otherwise, both are negative, so we need to flip the sense of the
    \\         // comparison to get the correct result.  (This assumes a twos- or ones-
    \\         // complement integer representation; if integers are represented in a
    \\         // sign-magnitude representation, then this flip is incorrect).
    \\         if (aInt > bInt) {
    \\             return .Less;
    \\         } else if (aInt == bInt) {
    \\             return .Equal;
    \\         } else return .Greater;
    \\     }
    \\ }
    \\
    \\ fn __aeabi_dcmpeq(a: f64, b: f64) callconv(.{ .arm_aapcs = .{} }) i32 {
    \\     return @intFromBool(cmpf2(f64, LE, a, b) == .Equal);
    \\ }
    \\
    \\ fn __aeabi_dcmplt(a: f64, b: f64) callconv(.{ .arm_aapcs = .{} }) i32 {
    \\     return @intFromBool(cmpf2(f64, LE, a, b) == .Less);
    \\ }
    \\
    \\ fn __aeabi_cdcmpeq_check_nan(a: f64, b: f64) callconv(.c) i32 {
    \\     return @intFromBool(std.math.isNan(a) or std.math.isNan(b));
    \\ }
    \\
    \\ export fn __aeabi_cdcmpeq(_: f64, _: f64) callconv(.naked) void {
    \\     const apsr_c = 0x20000000;
    \\     asm volatile (
    \\         \\        push {r0-r3, lr}
    \\         \\        bl %[__aeabi_cdcmpeq_check_nan]
    \\         \\        cmp r0, #1
    \\         \\        pop {r0-r3, lr}
    \\         \\        bne %[__aeabi_cdcmple]
    \\         \\        msr APSR_nzcvq, %[APSR_C]
    \\         \\        bx lr
    \\         :
    \\         : [__aeabi_cdcmple] "X" (&__aeabi_cdcmple),
    \\           [__aeabi_cdcmpeq_check_nan] "X" (&__aeabi_cdcmpeq_check_nan),
    \\           [APSR_C] "i" (apsr_c),
    \\     );
    \\ }
    \\
    \\ export fn __aeabi_cdcmple(_: f64, _: f64) callconv(.naked) void {
    \\     const apsr_c = 0x20000000;
    \\     const apsr_z = 0x40000000;
    \\     asm volatile (
    \\         \\        push {r0-r3, lr}
    \\         \\        bl  %[__aeabi_dcmplt]
    \\         \\        cmp r0, #1
    \\         \\        moveq ip, #0
    \\         \\        beq 1f
    \\         \\        ldm sp, {r0-r3}
    \\         \\        bl %[__aeabi_dcmpeq]
    \\         \\        cmp r0, #1
    \\         \\        moveq ip, %[APSR_CZ]
    \\         \\        movne ip, %[APSR_C]
    \\         \\1:
    \\         \\        msr APSR_nzcvq, ip
    \\         \\        pop {r0-r3}
    \\         \\        pop {pc}
    \\         :
    \\         : [__aeabi_dcmplt] "X" (&__aeabi_dcmplt),
    \\           [__aeabi_dcmpeq] "X" (&__aeabi_dcmpeq),
    \\           [APSR_C] "i" (apsr_c),
    \\           [APSR_CZ] "i" (apsr_c | apsr_z),
    \\     );
    \\ }
;
