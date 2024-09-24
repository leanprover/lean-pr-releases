/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.LeanOptions

namespace Lake

/--
Lake equivalent of CMake's
[`CMAKE_BUILD_TYPE`](https://stackoverflow.com/a/59314670).
-/
inductive BuildType
  /--
  Debug optimization, asserts enabled, custom debug code enabled, and
  debug info included in executable (so you can step through the code with a
  debugger and have address to source-file:line-number translation).
  For example, passes `-Og -g` when compiling C code.
  -/
  | debug
  /--
  Optimized, *with* debug info, but no debug code or asserts
  (e.g., passes `-O3 -g -DNDEBUG` when compiling C code).
  -/
  | relWithDebInfo
  /--
  Same as `release` but optimizing for size rather than speed
  (e.g., passes `-Os -DNDEBUG` when compiling C code).
  -/
  | minSizeRel
  /--
  High optimization level and no debug info, code, or asserts
  (e.g., passes `-O3 -DNDEBUG` when compiling C code).
  -/
  | release
deriving Inhabited, Repr, DecidableEq, Ord

/--
Ordering on build types. The ordering is used to determine
the *minimum* build version that is necessary for a build.
-/
instance : LT BuildType := ltOfOrd
instance : LE BuildType := leOfOrd
instance : Min BuildType := minOfLe
instance : Max BuildType := maxOfLe

/--
Compiler backend with which to compile Lean.
-/
inductive Backend
  /--
  Force the C backend.
  -/
  | c
  /--
  Force the LLVM backend.
  -/
  | llvm
  /--
  Use the default backend. Can be overridden by more specific configuration.
  -/
  | default
deriving Repr, DecidableEq

instance : Inhabited Backend := ⟨.default⟩

def Backend.ofString? (s : String) : Option Backend :=
  match s with
  | "c" => some .c
  | "llvm" => some .llvm
  | "default" => some .default
  | _ => none

protected def Backend.toString (bt : Backend) : String :=
  match bt with
  | .c => "c"
  | .llvm => "llvm"
  | .default => "default"

instance : ToString Backend := ⟨Backend.toString⟩

/--
If the left backend is default, choose the right one.
Otherwise, keep the left one.
This is used to implement preferential choice of backends,
where the library config can refine the package config.
Formally, a left absorbing monoid on {`C`, `LLVM`} with `Default` as the unit.
-/
def Backend.orPreferLeft : Backend → Backend → Backend
| .default, b => b
| b, _ => b

/-- The arguments to pass to `leanc` based on the build type. -/
def BuildType.leancArgs : BuildType → Array String
| debug => #["-Og", "-g"]
| relWithDebInfo => #["-O3", "-g", "-DNDEBUG"]
| minSizeRel => #["-Os", "-DNDEBUG"]
| release => #["-O3", "-DNDEBUG"]

def BuildType.ofString? (s : String) : Option BuildType :=
  match s with
  | "debug" => some .debug
  | "relWithDebInfo" => some .relWithDebInfo
  | "minSizeRel" => some .minSizeRel
  | "release" => some .release
  | _ => none

protected def BuildType.toString (bt : BuildType) : String :=
  match bt with
  | .debug => "debug"
  | .relWithDebInfo => "relWithDebInfo"
  | .minSizeRel => "minSizeRel"
  | .release => "release"

instance : ToString BuildType := ⟨BuildType.toString⟩

/-- Option that is used by Lean as if it was passed using `-D`. -/
structure LeanOption where
  name  : Lean.Name
  value : Lean.LeanOptionValue
  deriving Inhabited, Repr

/-- Formats the lean option as a CLI argument using the `-D` flag. -/
def LeanOption.asCliArg (o : LeanOption) : String :=
  s!"-D{o.name}={o.value.asCliFlagValue}"

/-- Configuration options common to targets that build modules. -/
structure LeanConfig where
  /--
  The mode in which the modules should be built (e.g., `debug`, `release`).
  Defaults to `release`.
  -/
  buildType : BuildType := .release
  /--
  Additional options to pass to both the Lean language server
  (i.e., `lean --server`) launched by `lake serve` and to `lean`
  when compiling a module's Lean source files.
  -/
  leanOptions : Array LeanOption := #[]
  /--
  Additional arguments to pass to `lean`
  when compiling a module's Lean source files.
  -/
  moreLeanArgs : Array String := #[]
  /--
  Additional arguments to pass to `lean`
  when compiling a module's Lean source files.

  Unlike `moreLeanArgs`, these arguments do not affect the trace
  of the build result, so they can be changed without triggering a rebuild.
  They come *before* `moreLeanArgs`.
  -/
  weakLeanArgs : Array String := #[]
  /--
  Additional arguments to pass to `leanc`
  when compiling a module's C source files generated by `lean`.

  Lake already passes some flags based on the `buildType`,
  but you can change this by, for example, adding `-O0` and `-UNDEBUG`.
  -/
  moreLeancArgs : Array String := #[]
  /--
  Additional options to pass to the Lean language server
  (i.e., `lean --server`) launched by `lake serve`.
  -/
  moreServerOptions : Array LeanOption := #[]
  /--
  Additional arguments to pass to `leanc`
  when compiling a module's C source files generated by `lean`.

  Unlike `moreLeancArgs`, these arguments do not affect the trace
  of the build result, so they can be changed without triggering a rebuild.
  They come *before* `moreLeancArgs`.
  -/
  weakLeancArgs : Array String := #[]
  /--
  Additional arguments to pass to `leanc` when linking (e.g., for shared
  libraries or binary executables). These will come *after* the paths of
  external libraries.
  -/
  moreLinkArgs : Array String := #[]
  /--
  Additional arguments to pass to `leanc` when linking (e.g., for shared
  libraries or binary executables). These will come *after* the paths of
  external libraries.

  Unlike `moreLinkArgs`, these arguments do not affect the trace
  of the build result, so they can be changed without triggering a rebuild.
  They come *before* `moreLinkArgs`.
  -/
  weakLinkArgs : Array String := #[]
  /--
  Compiler backend that modules should be built using (e.g., `C`, `LLVM`).
  Defaults to `C`.
  -/
  backend : Backend := .default
  /--
  Asserts whether Lake should assume Lean modules are platform-independent.

  * If `false`, Lake will add `System.Platform.target` to the module traces
  within the code unit (e.g., package or library). This will force Lean code
  to be re-elaborated on different platforms.

  * If `true`, Lake will exclude platform-dependent elements
  (e.g., precompiled modules, external libraries) from a module's trace,
  preventing re-elaboration on different platforms. Note that this will not
  effect modules outside the code unit in question. For example, a
  platform-independent package which depends on a platform-dependent library
  will still be platform-dependent.

  * If `none`, Lake will construct traces as natural. That is, it will include
  platform-dependent artifacts in the trace if they module depends on them,
  but otherwise not force modules to be platform-dependent.

  There is no check for correctness here, so a configuration can lie
  and Lake will not catch it. Defaults to `none`.
  -/
  platformIndependent : Option Bool := none
deriving Inhabited, Repr
