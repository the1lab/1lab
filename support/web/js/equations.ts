import { equationSetting, hiddenCodeSetting, serifFontSetting } from "./lib/settings";

window.addEventListener("DOMContentLoaded", () => {

  /* I tried really hard to do this with only CSS but :first-of-type is
   * only for *type*, and there'll be a div before the first comment (the
   * narrow screen navigation). So this bit of JS adds the
   * `first-comment` class to the first commented-out block so we can get
   * rid of its top margin. */
  const firstComment = Array.from(document.querySelector("article")?.children ?? [])
    .filter(e => e instanceof HTMLDivElement && e.classList.contains("commented-out"));

  if (firstComment.length >= 1) {
    firstComment[0].classList.add("first-comment");
  }

  hiddenCodeSetting.onChange((t) => {
    if (t) {
      document.querySelectorAll("details").forEach(d => d.setAttribute("open", "true"))
    } else {
      document.querySelectorAll("details").forEach(d => d.removeAttribute("open"))
    }
  });

  const buttons: NodeListOf<HTMLInputElement> = document.querySelectorAll("input.equations");

  buttons.forEach(button => {
    if (!button.classList.contains("narrow-only")) {
      button.style.display = "block";
    }

    equationSetting.onChange((t) => {
      if (button.checked !== undefined) button.checked = t;
      button.innerText = t ? "Hide equations" : "Show equations";
    });

    button.onclick = () => {
      equationSetting.toggle();
    };
  });

  const toggleFont = document.getElementById("toggle-fonts") as HTMLInputElement | null;

  if (toggleFont) {
    serifFontSetting.onChange((t) => {
      window.requestAnimationFrame(() => { toggleFont.checked = t });
    });
    toggleFont.onclick = () => serifFontSetting.toggle();
  }

  const showHiddenCode = document.getElementById("sidebar-hidden") as HTMLInputElement | null;
  if (showHiddenCode) {
    showHiddenCode.onclick = () => hiddenCodeSetting.toggle();
    hiddenCodeSetting.onChange((t) => {
      window.requestAnimationFrame(() => { showHiddenCode.checked = t });
    });
  }

  scrollToHash();
});

window.addEventListener("hashchange", scrollToHash);

function scrollToHash() {
  if (window.location.hash === '') return;

  const id = window.location.hash.slice(1);
  // #id doesn't work with numerical IDs
  const elem = document.querySelector(`[id="${id}"]`);
  if (!(elem instanceof HTMLElement)) return;
  // If the element is in a commented-out block or a <details> tag, unhide it
  // and scroll to it.
  const commentedOut = elem.closest('.commented-out') as HTMLElement | null;
  if (commentedOut)
    commentedOut.style.display = 'revert';
  const details = elem.closest('details') as HTMLElement | null;
  if (details)
    details.setAttribute("open", "");
  if (commentedOut || details)
    elem.scrollIntoView();
}

export { };
