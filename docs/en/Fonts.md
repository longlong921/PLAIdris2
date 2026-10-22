# Fonts

Typography matters in a proof because a similar-looking symbol can denote a different operation. Our implementation uses ordinary ASCII identifiers for Idris names, while prose may use mathematical Unicode such as `λ`, `→`, `∀`, `∃` and `⊑`. The source remains the authority when a display font makes two characters hard to distinguish.

## Readable on your machine {#fonts}

The site requests system UI fonts for text and a local monospace stack for code: Iosevka, JetBrains Mono, DejaVu Sans Mono, Liberation Mono, then the browser's monospace fallback. Chinese text falls back to installed CJK fonts. No font service is contacted, no font binary is bundled, and there is no prerequisite paid font.

If a symbol becomes an empty box, install a local font with the appropriate Unicode coverage or change the browser's default font. If a ligature makes `->` look like a single arrow, remember that the source still contains two ASCII characters. Copy from the downloadable source when precision matters.

## Symbols used in the exposition {#symbols}

| Display | Read as | Role |
| --- | --- | --- |
| `A → B` | a function from A to B | host function or object arrow type, as specified |
| `M —→ N` | M takes one step to N | an inductively defined relation |
| `M —↠ N` | zero or more steps | reflexive transitive closure |
| `Γ ⊢ M : A` | M has type A in Γ | a typing judgment |
| `v ⊑ w` | v contains no more information than w | the Part 3 information preorder |
| `⊥` | no finite information | a semantic value, not an exception |

The distinction between a host function arrow and an object-language reduction arrow is mathematical, not merely visual. Read the surrounding definition before relying on the glyph. [Equality](Equality.md) also separates definitional computation from an explicit equality proof.

## Accessibility {#accessibility}

Text can be enlarged without losing the chapter navigation. Wide code blocks scroll locally, the mobile menu has a keyboard-operable button, and the page begins with a skip-to-content link. The stylesheet respects reduced-motion preferences and provides a print layout. A language switch retains a shared section fragment, so a reader can compare the explanation without finding the section again.
