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

instance : ToString Status where
  toString
  | .missing => "missing"
  | .notStated => "not stated"
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

def info_for (n : Name) : Lean.CoreM (Option (System.FilePath × Name) × Option DeclarationRange × Status) := do
  let e ← getEnv
  let some d := e.find? n | return (none, none, .missing)
  let s ← status_of d
  let fn := getModuleNameFor? e n
  let p := DeclarationRanges.range <$> (← Lean.findDeclarationRanges? n)
  let fs ← match fn with
  | none => pure none
  | some fn => (do
    let f ← project_file_split (←Lean.findOLean fn)
    pure (f.2, fn))
  pure (fs, p, s)

def commit_sha : IO String :=
  String.trim <$> IO.Process.run { cmd := "git", args := #["rev-parse", "HEAD"] }

def get_url : IO (System.FilePath → Option DeclarationRange → String) := do
  let sha ← commit_sha
  return fun s p => url ++ "/blob/" ++ sha ++ "/" ++ s.toString ++ match p with
    | some r => s!"#L{r.pos.line}-L{r.endPos.line}"
    | none => ""

def make_svg (cells : List (ℕ × String × Option String × Status))
    (sections : Array (String × ℕ × ℕ)): Id String := do
  let mut counts := Std.mkHashMap
  for s in [Status.missing, Status.notStated, Status.stated, Status.proved] do
    counts := counts.insert s 0
  for (_, _, _, s) in cells do
    counts := counts.modify s (fun _ v => v + 1)

  let svg := fun c =>
    f!"<svg id=\"svg\" width=\"{550*2}\" height=\"95\" version=\"1.1\" xmlns=\"http://www.w3.org/2000/svg\">"
    ++ "<style>" ++ .nest 2 (
      "text { fill: gray; font-size: 16px; font-family: -apple-system,BlinkMacSystemFont,\"Segoe UI\",\"Noto Sans\",Helvetica,Arial,sans-serif,\"Apple Color Emoji\",\"Segoe UI Emoji\"}"
    ) ++ "</style>"
    ++ c ++
    "</svg>"
  let width := 2
  let rects ← cells.mapM (fun (i, n, f, d) => do
    let r := f!"
      <rect fill=\"{color d}\" x=\"{i*width}\" y=\"25\" width=\"{width}\" height=\"25\">
        <title>{n}</title>
      </rect>"
    match f with
    | none => r
    | some f => pure f!"<a href=\"{f}\">{r}</a>")

  let legendEntries ← counts.toList.mapM fun (k, v) => do
    f!"<tspan fill=\"{color k}\">{k}: {v} <tspan style=\"opacity: 0.75\">({v*100/cells.length}%)</tspan></tspan>"
  let legend := f!"<text x=\"0\" y=\"85\" width=\"{width*cells.length}\">{Format.joinSep legendEntries ", "}</text>"

  let titleEntries ← sections.toList.enum.mapM (fun (i, sn, s, e) => do
    let y := if i % 2 = 0 then 23 else 52
    let (anchor, x) := if i = sections.size - 1 then
        ("end", (e*width : ℚ))
      else
        ("middle", ((s + e)*width/2 : ℚ))
    return f!"<text text-anchor=\"{anchor}\" x=\"{x}\" y=\"{if i % 2 = 0 then 20 else 66}\" width=\"{(e-s)*width}\">{sn}</text>" ++
      f!"<line x1=\"{s*width}\" x2=\"{e*width}\" y1=\"{y}\" y2=\"{y}\" stroke=\"gray\" stroke-width=\"2\" />")

  toString $ svg (Format.joinSep rects "\n" ++ legend ++ Format.joinSep titleEntries "\n")
where
  color : Status → String
    | .missing => "darkred"
    | .notStated => "red"
    | .stated => "yellow"
    | .proved => "green"

def getTitle (n : Name) : CoreM String := do
  let some doc := Lean.getModuleDoc? (←getEnv) n | throwError "no docstring"
  if h : 0 < doc.size then
    let s := (doc[0]'h).doc
    let i := s.find (· = '#')
    return String.trim <| s.extract (s.next i) (s.findAux (· = '\n') s.endPos i)
  throwError "no docstring"

def printSvg : CoreM String := do
  let get_url ← get_url
  let infos ← (List.range' 0 550).mapM (fun i => do
    let n := (`MatrixCookbook).str ("eq_" ++ toString (i + 1))
    let data ← info_for n
    return (i, n.toString, data))
  let decls ← infos.mapM (fun (i, n, f, p, s) => do
    let f := (get_url ·.1 p) <$> f
    pure (i, n, f, s))
  let mut lastf := none
  let mut lastn := 0
  let mut sections := #[]
  for (i, _, f, _, _) in infos do
    let some (_, fn) := f | continue
    if let some lastf' := lastf then
      if fn ≠ lastf' then
        sections := sections.push (lastf', (lastn, i))
        lastn := i
    lastf := some fn
  sections := sections.push (lastf.get!, (lastn, infos.length))
  let mut shortNames := Std.mkHashMap
  shortNames := shortNames.insert "Solutions and Decompositions" "Decompositions"
  shortNames := shortNames.insert "Statistics and Probability" "Statistics"
  shortNames := shortNames.insert "Multivariate Distributions" "MV Dists."
  let sections' ← sections.mapM fun (sn, ij) => do
    let t ← getTitle sn
    return (shortNames.findD t t, ij)
  return make_svg decls sections'

#eval do IO.print (← printSvg)
