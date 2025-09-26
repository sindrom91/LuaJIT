const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const minilua = b.addExecutable(.{
        .name = "minilua",
        .root_module = b.createModule(.{
            .target = target,
            .optimize = std.builtin.OptimizeMode.ReleaseFast, // TODO: Does not work in Debug.
        }),
    });
    minilua.linkLibC();
    minilua.addCSourceFile(.{ .file = b.path("src/host/minilua.c") });

    const genBuildvmArch = b.addRunArtifact(minilua);
    genBuildvmArch.addFileArg(b.path("dynasm/dynasm.lua"));
    genBuildvmArch.addArgs(&.{ "-D", "JIT", "-D", "WIN", "-D", "FPU", "-o" });
    const buildvmArch = genBuildvmArch.addOutputFileArg("generated/buildvm_arch.h");
    genBuildvmArch.addFileArg(b.path("src/vm_x64.dasc"));

    const genRelver = b.addSystemCommand(&.{ "git", "show", "-s", "--format=%ct", "--output" });
    const relver = genRelver.addOutputFileArg("generated/luajit_relver.txt");

    const genVersion = b.addRunArtifact(minilua);
    genVersion.addFileArg(b.path("src/host/genversion.lua"));
    genVersion.addFileArg(b.path("src/luajit_rolling.h"));
    genVersion.addFileArg(relver);
    const luajith = genVersion.addOutputFileArg("generated/luajit.h");
    genVersion.step.dependOn(&genRelver.step);

    const buildvm = b.addExecutable(.{
        .name = "buildvm",
        .root_module = b.createModule(.{
            .target = target,
            .optimize = std.builtin.OptimizeMode.ReleaseFast, // TODO: Does not work in Debug.
        }),
    });
    buildvm.linkLibC();
    const buildvmSources = [_][]const u8{
        "src/host/buildvm.c",
        "src/host/buildvm_asm.c",
        "src/host/buildvm_peobj.c",
        "src/host/buildvm_lib.c",
        "src/host/buildvm_fold.c",
    };
    for (buildvmSources) |f| buildvm.addCSourceFile(.{ .file = b.path(f) });
    buildvm.addIncludePath(b.path("src"));
    buildvm.addIncludePath(b.path("src/host"));
    buildvm.addIncludePath(buildvmArch.dirname());
    buildvm.addIncludePath(luajith.dirname());
    buildvm.step.dependOn(&genBuildvmArch.step);
    buildvm.step.dependOn(&genVersion.step);

    const genFolddef = b.addRunArtifact(buildvm);
    genFolddef.addArgs(&.{ "-m", "folddef", "-o" });
    const folddef = genFolddef.addOutputFileArg("generated/lj_folddef.h");
    genFolddef.addFileArg(b.path("src/lj_opt_fold.c"));

    const genLibdef = b.addRunArtifact(buildvm);
    genLibdef.addArgs(&.{ "-m", "libdef", "-o" });
    const libdef = genLibdef.addOutputFileArg("generated/lj_libdef.h");
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
    for (all_libs) |lib| genLibdef.addFileArg(b.path(lib));

    const genFfdef = b.addRunArtifact(buildvm);
    genFfdef.addArgs(&.{ "-m", "ffdef", "-o" });
    const ffdef = genFfdef.addOutputFileArg("generated/lj_ffdef.h");
    for (all_libs) |lib| genFfdef.addFileArg(b.path(lib));

    const genBcdef = b.addRunArtifact(buildvm);
    genBcdef.addArgs(&.{ "-m", "bcdef", "-o" });
    const bcdef = genBcdef.addOutputFileArg("generated/lj_bcdef.h");
    for (all_libs) |lib| genBcdef.addFileArg(b.path(lib));

    const genRecdef = b.addRunArtifact(buildvm);
    genRecdef.addArgs(&.{ "-m", "recdef", "-o" });
    const recdef = genRecdef.addOutputFileArg("generated/lj_recdef.h");
    for (all_libs) |lib| genRecdef.addFileArg(b.path(lib));

    const genLjvm = b.addRunArtifact(buildvm);
    genLjvm.addArgs(&.{ "-m", "peobj", "-o" });
    const ljvm = genLjvm.addOutputFileArg("generated/lj_vm.obj");

    const libluajit = b.addLibrary(.{
        .name = "libluajit",
        .linkage = .static,
        .root_module = b.createModule(.{
            .optimize = optimize,
            .target = target,
        }),
    });
    libluajit.linkLibC();
    const libluajitSources = [_][]const u8{
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
    for (libluajitSources) |f| libluajit.addCSourceFile(.{ .file = b.path(f) });
    libluajit.addCSourceFile(.{ .file = ljvm, .flags = &.{} });
    libluajit.addIncludePath(b.path("src"));
    libluajit.addIncludePath(b.path("src/host"));
    libluajit.addIncludePath(folddef.dirname());
    libluajit.addIncludePath(libdef.dirname());
    libluajit.addIncludePath(ffdef.dirname());
    libluajit.addIncludePath(bcdef.dirname());
    libluajit.addIncludePath(recdef.dirname());
    libluajit.addIncludePath(luajith.dirname());

    libluajit.step.dependOn(&genFolddef.step);
    libluajit.step.dependOn(&genLibdef.step);
    libluajit.step.dependOn(&genFfdef.step);
    libluajit.step.dependOn(&genBcdef.step);
    libluajit.step.dependOn(&genRecdef.step);
    libluajit.step.dependOn(&genLjvm.step);
    libluajit.step.dependOn(&genVersion.step);

    const luajit = b.addExecutable(.{
        .name = "luajit",
        .root_module = b.createModule(.{
            .target = target,
            .optimize = optimize,
        }),
    });
    luajit.linkLibC();
    luajit.addCSourceFile(.{ .file = b.path("src/luajit.c") });
    luajit.addIncludePath(b.path("src"));
    luajit.addIncludePath(luajith.dirname());
    luajit.linkLibrary(libluajit);
    luajit.step.dependOn(&genVersion.step);

    b.installArtifact(luajit);
}
