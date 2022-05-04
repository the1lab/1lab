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

const fiItem = "1lab.footnote_inline";
let unfold_footnotes = false;
if (window.localStorage.getItem(fiItem) === "displayed") {
  unfold_footnotes = true;
}

document.addEventListener("DOMContentLoaded", () => {
  let footnotes = false;
  document.querySelectorAll("a.footnote-ref").forEach(elem => {
    const link = elem as HTMLAnchorElement;

    const referent = document.querySelector("li" + link.hash)!;
    const saved = link.cloneNode(true);
    link.draggable = false;
    if (referent.childElementCount > 1 || referent.childNodes[0].nodeName !== "P") {
      return;
    }

    footnotes = true;

    const insides = referent.childNodes[0].cloneNode(true);
    const ret = createReturn();

    link.onclick = (ev) => {
      if (!unfold_footnotes) { return; }

      if (ev.target === link || (ev.target as Node).nodeName !== "A") {
        ev.preventDefault();
      }

      if (link.classList.contains("unfolded-footnote") && ev.target === ret) {
        ev.preventDefault();
        link.replaceChildren(...Array.from(saved.childNodes).map(x => x.cloneNode(true)));
        link.classList.remove("unfolded-footnote");
        if (link.classList.contains("hover-highlight")) {
          link.classList.remove("hover-highlight");
        }
        return;
      }

      if (!link.classList.contains("unfolded-footnote")) {
        ev.preventDefault();
        link.replaceChildren(...Array.from(insides.childNodes)
          .map(x => x.cloneNode(true))
          .slice(0, -1));
        link.prepend(" (");
        link.prepend(ret);
        link.classList.add("unfolded-footnote");
        link.append(")");
      }
    };
  });

  if (footnotes) {
    const fnctl = document.getElementById("footnote-control")!;
    fnctl.style.display = "flex";
    const selected = document.querySelector("span#footnote-control > input") as HTMLInputElement;

    selected.checked = unfold_footnotes;
    selected.onchange = () => {
      unfold_footnotes = selected.checked;
      window.localStorage.setItem(fiItem, selected.checked ? "displayed" : "hidden");
    };
  }
});

export {};