// Arithmatex preserves TeX through Markdown; MathJax typesets those elements.
window.MathJax = {
  options: {
    processHtmlClass: "arithmatex",
    ignoreHtmlClass: ".*"
  },
  tex: {
    displayMath: [["\\[", "\\]"]],
    inlineMath: [["\\(", "\\)"]]
  }
};
