// Flags cookbook equations that are not yet stated in Lean, and theorems that are not yet proved.
//
// The statuses match `analyze.lean` (which draws the progress bar):
// * "not stated": there is no `eq_n` theorem for equation (n), or its statement is a
//   `(sorry : Prop)` placeholder;
// * "unproved": the statement is real but the proof uses `sorry`.
document.addEventListener("DOMContentLoaded", () => {
  const content = document.querySelector(".code-content");
  if (!content) return;

  const mark = (box, status) => {
    box.classList.add(`status-${status}`);
    box.dataset.status = status === "not-stated" ? "not stated" : "unproved";
    // The docstring just before a theorem's code holds the cookbook equation it formalizes.
    const doc = box.previousElementSibling;
    if (doc && doc.matches(".verso-text.mod-doc:not([id])")) {
      doc.classList.add(`status-${status}`);
    }
  };

  // Theorems whose code contains Lean's "declaration uses `sorry`" warning (embedded in the page's
  // hover data) are not proved, or not stated if the statement itself is `sorry`.
  for (const box of content.querySelectorAll(":scope > .code-box")) {
    const usesSorry = [...box.querySelectorAll(".verso-message.warning")].some(m =>
      /declaration uses [`']?sorry/.test(m.textContent));
    if (!usesSorry) continue;
    const code = [...box.querySelectorAll("code.hl.lean.block")].map(c => {
      const copy = c.cloneNode(true);
      copy.querySelectorAll(".hover-container").forEach(h => h.remove());
      return copy.textContent;
    }).join("\n");
    mark(box, /:\s*\(\s*sorry\s*:\s*Prop\s*\)/.test(code) ? "not-stated" : "unproved");
  }

  // Equations numbered `\tag{n}` in the cookbook text with no `eq_n` theorem on the page.
  const stated = new Set();
  for (const el of content.querySelectorAll('[id^="MatrixCookbook___eq_"]')) {
    const m = /^MatrixCookbook___eq_(\d+)/.exec(el.id);
    if (m) stated.add(Number(m[1]));
  }
  for (const quote of content.querySelectorAll("blockquote")) {
    // Read the TeX source, whether or not KaTeX has rendered it yet.
    const tex = [...quote.querySelectorAll("code.math")].map(m =>
      m.querySelector('annotation[encoding="application/x-tex"]')?.textContent ?? m.textContent
    ).join(" ");
    const missing = [...tex.matchAll(/\\tag\{(\d+)\}/g)].map(m => Number(m[1]))
      .filter(n => !stated.has(n));
    if (missing.length === 0) continue;
    quote.classList.add("status-not-stated");
    const note = document.createElement("p");
    note.className = "status-placeholder status-not-stated";
    note.textContent = `Not yet stated in Lean (${missing.map(n => `eq_${n}`).join(", ")}).`;
    quote.after(note);
  }
});
