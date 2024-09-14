// ! setup
#import "@preview/ctheorems:1.1.2": *
// ! font sizes
#let fontsizes = (
  normal: 12pt,
  section: 14pt,
  subsection: 12pt,
  large: 20pt,
  small: 8pt
)
// ! colours
#let solarized = (
  yellow: rgb("#b58900"),
  orange: rgb("#cb4b17"),
  red: rgb("#dc322f"),
  magenta: rgb("#d33682"),
  violet: rgb("#6c71c4"),
  blue: rgb("#268bd2"),
  cyan: rgb("#2aa198"),
  cyanlight: rgb("#d4ecea"),
  green: rgb("#859900"),
  base2: rgb("#eee8d5"),
  gray: rgb("#f2f2f2")
)

#let conf(
  course_code: none,
  course_title: none,
  subtitle: none,
  semester: none,
  professor: none,
  author: "Louis Meunier",
  // abstract: [],
  doc,
) = {
  v(4em)
  set align(left)
  text(25pt, course_code, weight:"bold") + text(25pt, " - " + course_title)
  text(12pt, "\n"+subtitle)
  // if cute != none {
  //   // set align(center)
  //  figure(
  //     image(cute, width: 40%)
  //   ) 
  // }
  // set align(left)
  text(12pt, "\n\nBased on lectures from "+ semester + " by " + professor + ".")
  text(12pt, "\nNotes by " + author)

  set par(
    first-line-indent: 1em,
    leading: 0.8em,
    linebreaks: "simple"
  )
  // let count = authors.len()
  // let ncols = calc.min(count, 3)
  // grid(
  //   columns: (1fr,) * ncols,
  //   row-gutter: 24pt,
  //   ..authors.map(author => [
  //     #author.name \
  //     #author.affiliation \
  //     #link("mailto:" + author.email)
  //   ]),
  // )

  // par(justify: false)[
  //   *Abstract* \
  //   #abstract
  // ]

  v(2em)
  outline(indent: 1em)
  
  set page(
    margin: 1.5cm,
    footer-descent: 60%
  )

  set text(
    font: "Linux Libertine",
    size: fontsizes.normal
  )
  // #show raw: set text(font: "Palatino")
  show link: set text(fill: solarized.cyan)
  show link: underline

  set align(left)
  show: thmrules.with(qed-symbol: $square.small.filled$)

  // ! headers
  set heading(numbering: "1.1")

  show heading.where(
    level: 1
  ): it =>text(
    size: fontsizes.section,
    weight: "bold",
    if (it.numbering != none) {
      par(leading: 0em, counter(heading).display(it.numbering) + h(.5em) + smallcaps(it.body) +"\n")
    } else {
      par(leading: 0em, it.body + [.]+"\n")
    }
  )
  
  show heading.where(
    level: 2
  ): it => text(
    size: fontsizes.subsection,
    weight: "semibold",
    // style: "italic",
    par(leading: 0em, first-line-indent: 0em, counter(heading).display(it.numbering) + h(.5em) + it.body)
    // it.numbering + h(.5em) + it.body + [.],
  )

  // ! this is the footer
  set page(footer: context [
    #let elems = query(
      selector(heading).before(here())
    )
    #let subsection = elems.last().body
    #let num = counter(heading).display(elems.last().numbering)

    #text(num, size: fontsizes.small)
    #text(subsection, size: fontsizes.small)
    #h(1fr)
    #text(counter(page).display(
      "1",
      // both: true,
    ),
    size: fontsizes.small
    )
  ])

  doc
}


// ! theorems
#let thmsettings = (
  inset: (top: 0.6em, left: .5em, right: .5em, bottom: 0.8em),
  base_level: 1
)

#let theorem = thmbox(
  "theorem", // identifier
  text($arrow.curve$+"Theorem", fill:solarized.red), // head
  fill: solarized.gray,
  inset: thmsettings.inset,
  // stroke: 1pt
  base_level: thmsettings.base_level
)

#let lemma = thmbox(
  "lemma", // identifier
  text($arrow.curve$+"Lemma", fill:solarized.orange), // head
  fill: solarized.gray,
  inset: thmsettings.inset,
  base_level: thmsettings.base_level
)

#let proposition = thmbox(
  "proposition", // identifier
  // $arrow.curve$+" Proposition",
  text($arrow.curve$ + "Proposition", fill:solarized.magenta), // head
  fill: solarized.gray,
  inset: thmsettings.inset,
  base_level: thmsettings.base_level
  // stroke: 1pt
)

#let corollary = thmbox(
  "corollary",
  // $arrow.curve$+" Corollary",
  text($arrow.curve$+"Corollary", fill:solarized.orange), // head
  fill: solarized.gray,
  inset: thmsettings.inset,
  base_level: thmsettings.base_level
)

#let definition = thmbox(
  "definition",
  // $arrow.curve$+" Definition",
  text($arrow.hook$ + "Definition", fill: solarized.blue),
  fill: solarized.gray,
  inset: thmsettings.inset,
  base_level: thmsettings.base_level
)

#let example = thmbox(
  "example",
  $ast.circle$+" Example",
  fill: solarized.cyanlight,
  inset: thmsettings.inset,
  base_level: thmsettings.base_level
)

#let remark = thmbox(
  "remark",
  "Remark",
  stroke: none,
  inset: (top: 0.4em, left: .5em, right: .5em, bottom: 0.6em),
)

#let proof = thmproof("proof", 
  text(
    smallcaps("Proof"),
    // highlight("Proof", fill: white, stroke: black, top-edge: "cap-height", extent: 3pt), 
    style: "oblique", 
    weight: "regular"
  ),
  inset: (top: 0em, left: 2.8em, right: 1.4em),
  separator: [#h(0.1em). #h(0.2em)],
)