/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis, Gabriel Ebner
-/
import tactic.lint
import system.io
import meta.rb_map  -- these are required
import all   -- then import everything, to parse the library for failing linters

/-!
# lint_mathlib

Script that runs the linters listed in `mathlib_linters` on all of mathlib.
As a side effect, the file `nolints.txt` is generated in the current
directory. This script needs to be run in the root directory of mathlib.

It assumes that files generated by `mk_all.sh` are present.

This is used by the CI script for mathlib.

Usage: `lean --run scripts/lint_mathlib.lean`
-/

open native

/--
Returns the contents of the `nolints.txt` file.
-/
meta def mk_nolint_file (env : environment) (mathlib_path_len : ℕ)
  (results : list (name × linter × rb_map name string)) : format := do
let failed_decls_by_file := rb_lmap.of_list (do
  (linter_name, _, decls) ← results,
  (decl_name, _) ← decls.to_list,
  let file_name := (env.decl_olean decl_name).get_or_else "",
  pure (file_name.popn mathlib_path_len, decl_name.to_string, linter_name.last)),
format.intercalate format.line $
"import .all" ::
"run_cmd tactic.skip" :: do
(file_name, decls) ← failed_decls_by_file.to_list.reverse,
"" :: ("-- " ++ file_name) :: do
(decl, linters) ← (rb_lmap.of_list decls).to_list.reverse,
pure $ "apply_nolint " ++ decl ++ " " ++ " ".intercalate linters

/--
Parses the list of lines of the `nolints.txt` into an `rb_lmap` from linters to declarations.
-/
meta def parse_nolints (lines : list string) : rb_lmap name name :=
rb_lmap.of_list $ do
line ← lines,
guard $ line.front = 'a',
_ :: decl :: linters ← pure $ line.split (= ' ') | [],
let decl := name.from_string decl,
linter ← linters,
pure (linter, decl)

open io io.fs

/--
Reads the `nolints.txt`, and returns it as an `rb_lmap` from linters to declarations.
-/
meta def read_nolints_file (fn := "scripts/nolints.txt") : io (rb_lmap name name) := do
cont ← io.fs.read_file fn,
pure $ parse_nolints $ cont.to_string.split (= '\n')

meta instance coe_tactic_to_io {α} : has_coe (tactic α) (io α) :=
⟨run_tactic⟩

/--
Writes a file with the given contents.
-/
meta def io.write_file (fn : string) (contents : string) : io unit := do
h ← mk_file_handle fn mode.write,
put_str h contents,
close h

/--
`write_nolints_for_decls outfile where_desc dir` runs the linters on every declaration
that appears in a file in directory `dir`. It prints the linter results and writes
a nolints file to `outfile`. `where_desc` is used to describe the target of the lint,
e.g. "in mathlib" or "in core".
-/
meta def write_nolints_for_decls (outfile where_desc dir : string) : io unit := do
env ← tactic.get_env,
decls ← tactic.decls_in_directory dir,
linters ← get_linters mathlib_linters,
let non_auto_decls := decls.filter (λ d, ¬ d.is_auto_or_internal env),
results₀ ← lint_core decls non_auto_decls linters,
nolint_file ← read_nolints_file $ "scripts/" ++ outfile,
let results := (do
  (linter_name, linter, decls) ← results₀,
  [(linter_name, linter, (nolint_file.find linter_name).foldl rb_map.erase decls)]),
io.print $ to_string $ format_linter_results env results decls non_auto_decls
  dir.length where_desc tt tt,
io.print_ln "\n",
io.write_file outfile $ to_string $ mk_nolint_file env dir.length results₀,
if results.all (λ r, r.2.2.empty) then pure () else io.fail ""

/-- Runs when called with `lean --run` -/
meta def main : io unit := do
ml ← succeeds $ tactic.get_mathlib_dir >>= write_nolints_for_decls "nolints.txt" "in mathlib",
core ← succeeds $ tactic.get_core_dir >>= write_nolints_for_decls "nolints_core.txt" "in core",
guardb $ ml && core
