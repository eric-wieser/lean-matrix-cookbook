import MatrixCookbook
import Lean.CoreM
import Lean.Util.Sorry
import Mathlib.Data.String.Defs

set_option autoImplicit false

open Lean

def url : String := "https://github.com/eric-wieser/lean-matrix-cookbook"

/-- Split a path into an Optional parent component and filename -/
def path_split (path : String) : Option String × String :=
  match (path.split (· = '/')).reverse with
  | [] => (none, "/")
  | [a] => (none, a)
  | (a :: as) => ("/".intercalate as.reverse, a)
/-- Split a lean path into a project/parent pair -/
def project_file_split (path : System.FilePath) : IO (Option System.FilePath × System.FilePath) :=
  do
    let path := path.withExtension "lean"
    (IO.iterate (path, (none : Option System.FilePath)) $ fun state => do
      let (p, old_rest) := state
      let some rest := p.fileName | throw default
      let rest := match old_rest with
      | some r => rest / r
      | none => rest
      let some parent := p.parent | return .inr (none, rest)
      let some pparent := parent.parent | return .inr (none, rest)
      let some ppparent := pparent.parent | return .inr (none, rest)
      if ← (ppparent / "lakefile.lean").pathExists then
        return .inr (ppparent, rest)
      else if "/lib/lean".data.IsSuffix parent.toString.data then
        return .inr (none, rest)
      else
        return .inl (parent, some rest))

inductive Status
  | missing
  | notStated
  | stated
  | proved
  deriving DecidableEq, Hashable

instance : Repr Status where
  reprPrec r _ := match r with
  | .missing => "missing"
  | .notStated => "notStated"
  | .stated => "stated"
  | .proved => "proved"

def status_of (d : ConstantInfo) : Lean.CoreM Status := do
  if d.type.hasSorry then
    return .notStated
  else
    let some v := d.value? | throwError "Axioms not permitted!"
    if v.hasSorry then
      return .stated
    else
      return .proved

def getModuleNameFor? (env : Environment) (nm : Name) : Option Name :=
  env.getModuleIdxFor? nm >>= fun i => env.header.moduleNames[i.toNat]?

def info_for (n : Name) : Lean.CoreM (Option System.FilePath × Option DeclarationRange × Status) := do
  let e ← getEnv
  let some d := e.find? n | return (none, none, .missing)
  let s ← status_of d
  let f := getModuleNameFor? e n
  let p := DeclarationRanges.range <$> (← Lean.findDeclarationRanges? n)
  let f ← match f with
  | none => pure none
  | some f => (do
    let f ← project_file_split (←Lean.findOLean f)
    pure f.2)
  pure (f, p, s)

def commit_sha : IO String :=
  String.trim <$> IO.Process.run { cmd := "git", args := #["rev-parse", "HEAD"] }

def get_url : IO (System.FilePath → Option DeclarationRange → String) := do
  let sha ← commit_sha
  return fun s p => url ++ "/blob/" ++ sha ++ "/" ++ s.toString ++ match p with
    | some r => s!"#L{r.pos.line}-L{r.endPos.line}"
    | none => ""

def make_svg (cells : List (ℕ × Option String × Status)) : Id String := do
  let svg := fun c =>
    f!"<svg id=\"svg\" width=\"{550*2}\" height=\"25\" version=\"1.1\" xmlns=\"http://www.w3.org/2000/svg\">"
    ++ c ++
    "</svg>"

  let rects ← cells.mapM (fun c : ℕ × Option String × Status => do
    let color := match c.2.2 with
    | .missing => "darkred"
    | .notStated => "red"
    | .stated => "yellow"
    | .proved => "green"
    let r := f!"
      <rect fill=\"{color}\" x=\"{c.1*2}\" y=\"0\" width=\"2\" height=\"25\">
        <title>{c.1}</title>
      </rect>"

    match c.2.1 with
    | none => r
    | some f => pure f!"<a href=\"{f}\">{r}</a>")
  toString $ svg (Format.joinSep rects "\n")

def printSvg : CoreM String := do
  let get_url ← get_url
  let decls ← (List.range' 1 551).mapM (fun i => do
    let n := (`MatrixCookbook).str ("eq_" ++ toString i)
    let (f, p, s) ← info_for n
    let f := (get_url · p) <$> f
    pure (i, f, s))
  return make_svg decls

#eval do IO.print (← printSvg)
