// Working builds:
// zig build -Dtarget=x86-windows
// zig build -Dtarget=x86_64-windows
// zig build -Dtarget=aarch64-windows
// zig build -Dtarget=x86-linux-musl
// zig build -Dtarget=x86_64-linux-musl
// zig build -Dtarget=arm-linux-musleabihf
// zig build -Dtarget=aarch64-linux-musl
// zig build -Dtarget=aarch64_be-linux-musl
// zig build -Dtarget=powerpc-linux-musleabi
// zig build -Dtarget=powerpc-linux-musleabihf

// Non-working builds:
// zig build -Dtarget=arm-linux-musleabi
// zig build -Dtarget=mips-linux-musleabi
// zig build -Dtarget=mips-linux-musleabihf
// zig build -Dtarget=mipsel-linux-musleabi
// zig build -Dtarget=mipsel-linux-musleabihf
// zig build -Dtarget=mips64-linux-musleabi
// zig build -Dtarget=mips64-linux-musleabihf
// zig build -Dtarget=mips64el-linux-musleabi
// zig build -Dtarget=mips64el-linux-musleabihf

const std = @import("std");

fn getTriple(alloc: std.mem.Allocator, t: std.Target) []u8 {
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

fn getTargetDefines(alloc: std.mem.Allocator, triple: []const u8) ![]u8 {
    var argv: std.ArrayList([]const u8) = .empty;
    defer argv.deinit(alloc);
    try argv.appendSlice(alloc, &.{
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
    });

    var child = std.process.Child.init(argv.items, alloc);
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;
    try child.spawn();

    const out = try child.stdout.?.readToEndAlloc(alloc, 10 * 1024 * 1024);
    const err = try child.stderr.?.readToEndAlloc(alloc, 128 * 1024);
    const term = try child.wait();

    switch (term) {
        .Exited => |code| if (code != 0) {
            std.debug.print("preprocess failed ({d}): {s}\n", .{ code, err });
            return error.PreprocessFailed;
        },
        else => {
            std.debug.print("preprocess failed: {s}\n", .{err});
            return error.PreprocessFailed;
        },
    }
    return out;
}

fn hasDefine(target_defines: []const u8, name: []const u8) bool {
    var lines = std.mem.tokenizeScalar(u8, target_defines, '\n');
    while (lines.next()) |line_raw| {
        const line = std.mem.trim(u8, line_raw, " \t\r");
        if (!std.mem.startsWith(u8, line, "#define ")) continue;
        var it = std.mem.tokenizeAny(u8, line[8..], " \t(");
        if (std.mem.eql(u8, it.next() orelse continue, name)) return true;
    }
    return false;
}

fn defineEquals(target_defines: []const u8, name: []const u8, value: []const u8) bool {
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

fn getTargetLjarch(target_defines: []const u8) []const u8 {
    if (hasDefine(target_defines, "LJ_TARGET_X64")) {
        return "x64";
    } else if (hasDefine(target_defines, "LJ_TARGET_X86")) {
        return "x86";
    } else if (hasDefine(target_defines, "LJ_TARGET_ARM")) {
        return "arm";
    } else if (hasDefine(target_defines, "LJ_TARGET_ARM64")) {
        return "arm64";
    } else if (hasDefine(target_defines, "LJ_TARGET_PPC")) {
        return "ppc";
    } else if (hasDefine(target_defines, "LJ_TARGET_MIPS")) {
        if (hasDefine(target_defines, "LJ_TARGET_MIPS64")) {
            return "mips64";
        } else {
            return "mips";
        }
    } else if (hasDefine(target_defines, "LJ_TARGET_PPC")) {
        return "ppc";
    } else {
        @panic("Unsupported architecture.");
    }
}

pub fn build(b: *std.Build) !void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const alloc = b.allocator;

    const arch = target.result.cpu.arch;
    const target_sys = target.result.os.tag;
    const host_sys = b.graph.host.result.os.tag;

    var host_flags: std.ArrayList([]const u8) = .empty;
    if (host_sys != target_sys) {
        // TODO: This is probably not the same as what Makefile does.
        switch (target_sys) {
            .windows => {
                try host_flags.append(alloc, "-malign-double");
                try host_flags.append(alloc, "-DLUAJIT_OS=LUAJIT_OS_WINDOWS");
            },
            .linux => try host_flags.append(alloc, "-DLUAJIT_OS=LUAJIT_OS_LINUX"),
            .macos => try host_flags.append(alloc, "-DLUAJIT_OS=LUAJIT_OS_OSX"),
            .ios => {
                try host_flags.append(alloc, "-DLUAJIT_OS=LUAJIT_OS_OSX");
                try host_flags.append(alloc, "-DTARGET_OS_IPHONE=1");
            },
            else => try host_flags.append(alloc, "-DLUAJIT_OS=LUAJIT_OS_OTHER"),
        }
    }

    const triple = getTriple(alloc, target.result);
    defer alloc.free(triple);
    const target_defines = try getTargetDefines(alloc, triple);
    const target_ljarch = getTargetLjarch(target_defines);
    var dasm_arch = target_ljarch;

    // Set up DASM flags.
    var dasm_flags: std.ArrayList([]const u8) = .empty;
    if (defineEquals(target_defines, "LJ_LE", "1")) {
        try dasm_flags.appendSlice(alloc, &.{ "-D", "ENDIAN_LE" });
    } else {
        try dasm_flags.appendSlice(alloc, &.{ "-D", "ENDIAN_BE" });
    }
    if (defineEquals(target_defines, "LJ_ARCH_BITS", "64"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "P64" });
    if (defineEquals(target_defines, "LJ_HASJIT", "1"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "JIT" });
    if (defineEquals(target_defines, "LJ_HASFFI", "1"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "FFI" });
    if (defineEquals(target_defines, "LJ_DUALNUM", "1"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "DUALNUM" });
    if (defineEquals(target_defines, "LJ_ARCH_HASFPU", "1"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "FPU" });
    if (!defineEquals(target_defines, "LJ_ABI_SOFTFP", "1"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "HFABI" });
    if (target_sys == .windows)
        try dasm_flags.appendSlice(alloc, &.{ "-D", "WIN" });
    if (defineEquals(target_defines, "LJ_NO_UNWIND", "1"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "NO_UNWIND" });
    if (defineEquals(target_defines, "LJ_ABI_PAUTH", "1"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "PAUTH" });
    if (std.mem.eql(u8, target_ljarch, "x64") and defineEquals(target_defines, "LJ_FR2", "1"))
        dasm_arch = "x86";
    if (std.mem.eql(u8, target_ljarch, "arm") and target_sys == .ios)
        try dasm_flags.appendSlice(alloc, &.{ "-D", "IOS" });
    if (hasDefine(target_defines, "LJ_TARGET_MIPSR6"))
        try dasm_flags.appendSlice(alloc, &.{ "-D", "MIPSR6" });
    if (std.mem.eql(u8, target_ljarch, "ppc")) {
        if (defineEquals(target_defines, "LJ_ARCH_SQRT", "1"))
            try dasm_flags.appendSlice(alloc, &.{ "-D", "SQRT" });
        if (defineEquals(target_defines, "LJ_ARCH_ROUND", "1"))
            try dasm_flags.appendSlice(alloc, &.{ "-D", "ROUND" });
        if (defineEquals(target_defines, "LJ_ARCH_PPC32ON64", "1"))
            try dasm_flags.appendSlice(alloc, &.{ "-D", "GPR64" });
        if (target_sys == .ps3)
            try dasm_flags.appendSlice(alloc, &.{ "-D", "PPE", "-D", "TOC" });
    }

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
    const dasc_file = try std.mem.concat(alloc, u8, &.{ "src/vm_", dasm_arch, ".dasc" });
    gen_buildvm_arch.addFileArg(b.path(dasc_file));

    const gen_relver = b.addSystemCommand(&.{ "git", "show", "-s", "--format=%ct", "--output" });
    const relver = gen_relver.addOutputFileArg("generated/luajit_relver.txt");

    const gen_version = b.addRunArtifact(minilua);
    gen_version.addFileArg(b.path("src/host/genversion.lua"));
    gen_version.addFileArg(b.path("src/luajit_rolling.h"));
    gen_version.addFileArg(relver);
    const luajith = gen_version.addOutputFileArg("generated/luajit.h");
    gen_version.step.dependOn(&gen_relver.step);

    var host = b.graph.host;

    // Set up HOST flags.
    if (hasDefine(target_defines, "LJ_TARGET_ARM64") and hasDefine(target_defines, "__AARCH64EB__")) {
        try host_flags.append(alloc, "-D__AARCH64EB__=1");
    } else if (hasDefine(target_defines, "LJ_TARGET_PPC")) {
        if (defineEquals(target_defines, "LJ_LE", "1")) {
            try host_flags.append(alloc, "-DLJ_ARCH_ENDIAN=LUAJIT_LE");
        } else {
            try host_flags.append(alloc, "-DLJ_ARCH_ENDIAN=LUAJIT_BE");
        }
    } else if (hasDefine(target_defines, "LJ_TARGET_MIPS") and hasDefine(target_defines, "MIPSEL")) {
        try host_flags.append(alloc, "-D__MIPSEL__=1");
    } else if (defineEquals(target_defines, "LJ_TARGET_PS3", "1")) {
        try host_flags.append(alloc, "-D__CELLOS_LV2__");
    }
    if (defineEquals(target_defines, "LJ_ARCH_HASFPU", "1")) {
        try host_flags.append(alloc, "-DLJ_ARCH_HASFPU=1");
    } else {
        try host_flags.append(alloc, "-DLJ_ARCH_HASFPU=0");
    }
    if (defineEquals(target_defines, "LJ_ABI_SOFTFP", "1")) {
        try host_flags.append(alloc, "-DLJ_ABI_SOFTFP=1");
    } else {
        try host_flags.append(alloc, "-DLJ_ABI_SOFTFP=0");
    }
    if (defineEquals(target_defines, "LJ_NO_UNWIND", "1")) {
        try host_flags.append(alloc, "-DLUAJIT_NO_UNWIND");
    }
    if (defineEquals(target_defines, "LJ_ABI_PAUTH", "1")) {
        try host_flags.append(alloc, "-DLJ_ABI_PAUTH=1");
    }

    if (target.result.ptrBitWidth() == 32) {
        if (b.graph.host.result.ptrBitWidth() == 64) {
            // TODO: This should work for other architectures, not just x86_64.
            host = b.resolveTargetQuery(.{
                .cpu_arch = .x86,
                .os_tag = host.result.os.tag,
                .abi = host.result.abi,
            });
        }
    }

    const buildvm = b.addExecutable(.{
        .name = "buildvm",
        .root_module = b.createModule(.{
            .target = host, // This is always executed on the host system!
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

    try host_flags.append(alloc, "-Wno-unknown-escape-sequence"); // TODO: Windows paths in #line cause errors.
    try host_flags.append(alloc, try std.mem.concat(alloc, u8, &.{ "-DLUAJIT_TARGET=LUAJIT_ARCH_", target_ljarch }));

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

    const cflags = if (arch == .arm)
        &[_][]const u8{
            "-DLUAJIT_UNWIND_EXTERNAL",
            "-D__floatdidf=__aeabi_l2d",
            "-D__floatundidf=__aeabi_ul2d",
            "-D__floatdisf=__aeabi_l2f",
            "-D__floatundisf=__aeabi_ul2f",
            "-D__fixdfdi=__aeabi_d2lz",
            "-D__fixunsdfdi=__aeabi_d2ulz",
            "-D__fixsfdi=__aeabi_f2lz",
            "-D__fixunssfdi=__aeabi_f2ulz",
        }
    else
        &[_][]const u8{"-DLUAJIT_UNWIND_EXTERNAL"};

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
    for (libluajit_sources) |f| libluajit.root_module.addCSourceFile(.{ .file = b.path(f), .flags = cflags });
    if (target_sys == .windows) {
        libluajit.root_module.addObjectFile(ljvm);
    } else {
        libluajit.root_module.addAssemblyFile(ljvm);
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
    luajit.root_module.addCSourceFile(.{ .file = b.path("src/luajit.c"), .flags = cflags });
    luajit.root_module.addIncludePath(b.path("src"));
    luajit.root_module.addIncludePath(luajith.dirname());
    luajit.root_module.linkLibrary(libluajit);
    luajit.step.dependOn(&gen_version.step);

    if (target_sys == .linux) {
        luajit.root_module.linkSystemLibrary("unwind", .{});
    }

    b.installArtifact(luajit);
}
