const createReturn = () => {
  const ret = document.createElement("a");
  ret.innerText = "❌";
  ret.style.cursor = "pointer";
  ret.style.paddingLeft = "0.25em";
  ret.style.verticalAlign = "super";
  ret.style.fontStyle = "normal";
  ret.style.fontSize = "10pt";
  ret.href = '';
  ret.title = "Collapse this footnote";
  return ret;
}

let unfold_footnotes = false;

document.addEventListener("DOMContentLoaded", () => {
  let footnotes = false;
  document.querySelectorAll("a.footnote-ref").forEach(elem => {
    const referent = document.querySelector("li" + elem.hash);
    const saved = elem.cloneNode(true);
    console.log(referent.childElementCount);
    if (referent.childElementCount > 1 || referent.childNodes[0].nodeName !== "P") {
      return;
    }

    footnotes = true;

    const insides = referent.childNodes[0].cloneNode(true);
    const ret = createReturn();
    console.log(insides);

    elem.onclick = (ev) => {
      if (!unfold_footnotes) { return; }

      if (ev.target === elem || ev.target.nodeName !== "A") {
        console.log(ev.target);
        ev.preventDefault();
      }

      if (elem.classList.contains("unfolded-footnote") && ev.target === ret) {
        ev.preventDefault();
        elem.replaceChildren(...Array(...saved.childNodes).map(x => x.cloneNode(true)));
        elem.classList.remove("unfolded-footnote");
        if (elem.classList.contains("hover-highlight")) {
          elem.classList.remove("hover-highlight");
        }
        return;
      }

      if (!elem.classList.contains("unfolded-footnote")) {
        ev.preventDefault();
        elem.replaceChildren(...Array(...insides.childNodes)
          .map(x => x.cloneNode(true))
          .slice(0, -1));
        elem.prepend(" (");
        elem.prepend(ret);
        elem.classList.add("unfolded-footnote");
        elem.append(")");
      }
    };
  });

  if (footnotes) {
    const fnctl = document.getElementById("footnote-control");
    fnctl.style.display = "flex";
    const selected = document.querySelector("span#footnote-control > input");
    selected.onchange = () => {
      unfold_footnotes = selected.checked;
    };
    unfold_footnotes = selected.checked;
  }
});
