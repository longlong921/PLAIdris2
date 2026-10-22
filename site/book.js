/* Shared by the live page and the Node behavior tests. No dependencies. */
(function (root) {
  "use strict";
  function languageTarget(href, hash) {
    return href.split("#")[0] + (hash || "");
  }
  if (typeof module !== "undefined") module.exports = { languageTarget };
  if (!root.document) return;
  const doc = root.document;
  const toggle = doc.getElementById("language-switch");
  if (toggle) {
    const target = toggle.getAttribute("href");
    const update = () => toggle.setAttribute("href", languageTarget(target, root.location.hash));
    root.addEventListener("hashchange", update);
    update();
  }
  const navButton = doc.getElementById("nav-toggle");
  if (navButton) navButton.addEventListener("click", () => {
    const expanded = navButton.getAttribute("aria-expanded") !== "true";
    navButton.setAttribute("aria-expanded", String(expanded));
    doc.getElementById("chapter-nav").classList.toggle("expanded", expanded);
  });
  const search = doc.getElementById("chapter-search");
  if (search) search.addEventListener("input", () => {
    const query = search.value.trim().toLocaleLowerCase();
    for (const item of doc.querySelectorAll("#chapter-nav li")) {
      item.hidden = !(item.textContent + " " + item.dataset.chapter).toLocaleLowerCase().includes(query);
    }
  });
})(typeof window === "undefined" ? globalThis : window);
