// Flags theorems that are not yet proved, or not yet stated, in the literate site.
//
// The statuses match `analyze.lean` (which draws the progress bar):
// * "not stated": the statement itself is `sorry`, written as `eq_n : (sorry : Prop) := sorry`;
// * "unproved": the statement is real but the proof uses `sorry`.
//
// Lean's "declaration uses `sorry`" warning is embedded in each code box's hover data, so a code box
// containing it is not proved. The class added to the box is also added to the docstring just before
// it, which holds the corresponding cookbook equation.
document.addEventListener("DOMContentLoaded", () => {
  for (const box of document.querySelectorAll(".code-content > .code-box")) {
    const usesSorry = [...box.querySelectorAll(".verso-message.warning")].some(m =>
      /declaration uses [`']?sorry/.test(m.textContent));
    if (!usesSorry) continue;

    // Only the code, not the embedded hover messages, decides whether the statement is `sorry`.
    const code = [...box.querySelectorAll("code.hl.lean.block")].map(c => {
      const copy = c.cloneNode(true);
      copy.querySelectorAll(".hover-container").forEach(h => h.remove());
      return copy.textContent;
    }).join("\n");
    const status = /:\s*\(\s*sorry\s*:\s*Prop\s*\)/.test(code) ? "not-stated" : "unproved";

    box.classList.add(`status-${status}`);
    box.dataset.status = status === "not-stated" ? "not stated" : "unproved";
    const doc = box.previousElementSibling;
    if (doc && doc.matches(".verso-text.mod-doc:not([id])")) {
      doc.classList.add(`status-${status}`);
    }
  }
});
