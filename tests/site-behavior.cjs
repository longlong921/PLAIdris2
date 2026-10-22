"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const vm = require("node:vm");
const { languageTarget } = require("../site/book.js");

for (const language of ["en", "zh"]) {
  for (const chapter of ["index", ...JSON.parse(fs.readFileSync("book/chapters.json")).map(c => c.id),
      ...JSON.parse(fs.readFileSync("book/extensions.json")).map(c => c.id)]) {
    const href = `../${language}/${chapter}.html`;
    for (const hash of ["", "#theorems", "#exercises", "#chapter-title", "#a%20b"]) {
      assert.equal(languageTarget(href, hash), href + hash);
      assert.equal(languageTarget(href + "#old", hash), href + hash);
    }
  }
}
// Exercise the actual browser event handlers using a small DOM contract, so a
// passing pure helper test cannot conceal an unconnected language-switch link.
const events = {};
const attributes = { href: "../zh/Untyped.html" };
const link = { getAttribute: key => attributes[key], setAttribute: (key, value) => attributes[key] = value };
const window = {
  location: { hash: "#examples" },
  addEventListener: (event, callback) => events[event] = callback,
  document: { getElementById: id => id === "language-switch" ? link : null },
};
vm.runInNewContext(fs.readFileSync("site/book.js", "utf8"), { window });
assert.equal(attributes.href, "../zh/Untyped.html#examples");
window.location.hash = "#theorems";
events.hashchange();
assert.equal(attributes.href, "../zh/Untyped.html#theorems");
window.location.hash = "";
events.hashchange();
assert.equal(attributes.href, "../zh/Untyped.html");
console.log("PASS all paired chapter language targets and actual hashchange handlers");
