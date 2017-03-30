----------------------------------------------------------------------------
-- LuaJIT ARM64BE disassembler wrapper module.
--
-- Copyright (C) 2005-2017 Mike Pall. All rights reserved.
-- Released under the MIT license. See Copyright Notice in luajit.h
----------------------------------------------------------------------------
-- This module just exports the big-endian functions from the
-- ARM64 disassembler module. All the interesting stuff is there.
------------------------------------------------------------------------------

local dis_arm64 = require((string.match(..., ".*%.") or "").."dis_arm64")
return {
  create = dis_arm64.create,
  disass = dis_arm64.disass,
  regname = dis_arm64.regname
}

