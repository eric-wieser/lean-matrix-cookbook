import matrix_cookbook

def url : string := "https://github.com/eric-wieser/lean-matrix-cookbook"

/-- Split a path into an optional parent component and filename -/
def path_split (path : string) : option string × string :=
match (path.split (= '/')).reverse with
| [] := (none, "/")
| [a] := (none, a)
| (a :: as) := ("/".intercalate as.reverse, a)
end

/-- Split a lean path into a project/parent pair -/
def project_file_split (path : string) : io (option string × string) :=
do
  (parent, some rest, tt) ← (io.iterate (some path, (none : option string), ff) $ λ state, do {
    (some p, old_rest, ff) ← pure state | pure none,
    (parent, rest) ← pure (path_split p),
    let rest := (match old_rest with
    | some r := rest ++ "/" ++ r
    | none := rest
    end),
    some parent ← pure parent | pure (some (parent, old_rest, tt)),
    found ← io.fs.file_exists (parent ++ "/leanpkg.toml"),
    if !found && "/lib/lean/library".is_suffix_of p then
      pure (some (none, some rest, tt))
    else
      pure (some (parent, some rest, found)) }),
  pure (parent, rest)

inductive status
| missing
| stated
| proved

instance : has_repr (status) :=
⟨λ r, match r with
| status.missing := "missing"
| status.stated := "stated"
| status.proved := "proved"
end⟩

meta instance : has_to_format (status) :=
⟨λ r, match r with
| status.missing := "missing"
| status.stated := "stated"
| status.proved := "proved"
end⟩

meta def status_of (n : name) : tactic status :=
do
  some d ← tactic.try_core (tactic.get_decl n) | pure status.missing,
  if d.type.contains_sorry then
    pure status.missing
  else if d.value.contains_sorry then
    pure status.stated
  else
    pure status.proved

meta def info_for (n : name) : tactic (option string × option pos × status) :=
do
  e ← tactic.get_env,
  s ← status_of n,
  (f : option string) ← tactic.try_core (e.decl_olean n),
  p ← tactic.try_core (e.decl_pos n),
  f ← match f with
  | none := pure f
  | some f := (do
    f ← tactic.unsafe_run_io (project_file_split f),
    pure f.2)
  end,
  pure (f, p, s)

meta def commit_sha : io string :=
io.cmd { cmd := "git", args := ["rev-parse", "HEAD"] }

meta def get_url : io (string → option pos → string) :=
do
  sha ← commit_sha,
  pure (λ s p, url ++ "/blob/" ++ sha ++ "/" ++ s ++ match p with
  | some ⟨r, c⟩ := "#L" ++ to_string r
  | none := ""
  end)

meta def make_svg (cells : list (ℕ × option string × status)) : id string :=
do
  let svg := λ c,
    format!/-"<svg id="svg" width="{550*2}" height="25" version="1.1" xmlns="http://www.w3.org/2000/svg">"-/
    ++ c ++ 
    /-"</svg>"-/,
  
  -- "-/  -- cursed highlighting fixer

  rects ← cells.mmap (λ c : ℕ × option string × status, do
    let color := match c.2.2 with
    | status.missing := "red"
    | status.stated := "yellow"
    | status.proved := "green"
    end,
    let r := format!/-"
      <rect fill="{color}" x="{c.1*2}" y="0" width="2" height="25">
        <title>{c.1}</title>
      </rect>"-/,

    -- "-/  -- cursed highlighting fixer
  
    match c.2.1 with
    | none := r
    | some f := pure format!/-"<a href="{f}">{r}</a>"-/
    end),
  to_string $ svg (format.intercalate "\n" rects)

meta def main : io unit := do
  get_url ← get_url,
  decls ← (list.range' 1 551).mmap (λ i, do
    let n := (`matrix_cookbook).mk_string ("eq_" ++ to_string i),
    (f, p, s) ← io.run_tactic (info_for n),
    let f := (λ f : string, get_url f p) <$> f,
    pure (i, f, s)),
  io.print (show string, from make_svg decls)