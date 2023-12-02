import { Setting } from "./lib/settings";

const equationSetting = new Setting<boolean>("display of equations", false).registerToggle();

const serifFontSetting = new Setting<boolean>("serif font", false)
  .registerToggle("Use serif font", "Use sans-serif font");

const hiddenCodeSetting = new Setting<boolean>("hidden code", false)
  .registerToggle("Display hidden code", "Do not display hidden code");

window.addEventListener("DOMContentLoaded", () => {

  equationSetting.onChange((t) => {
    if (t) {
      document.body.classList.add("show-equations");
    } else {
      document.body.classList.remove("show-equations");
    }
  });

  serifFontSetting.onChange((t) => {
    if (t) {
      document.body.classList.remove("sans-serif");
    } else {
      document.body.classList.add("sans-serif");
    }
  });

  hiddenCodeSetting.onChange((t) => {
    if (t) {
      document.body.classList.add("show-hidden-code");
      document.querySelectorAll("details").forEach(d => d.setAttribute("open", "true"))
    } else {
      document.body.classList.remove("show-hidden-code");
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
      if (t) {
        button.innerText = "Hide equations";
      } else {
        button.innerText = "Show equations";
      }
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
  if (window.location.hash != '') {
    const id = window.location.hash.slice(1);
    // #id doesn't work with numerical IDs
    const elem = document.querySelector(`[id="${id}"]`) as HTMLInputElement | null;
    if (elem) {
      // If the element is in a commented-out block or a <details> tag, unhide it
      // and scroll to it.
      const commentedOut = elem.closest('.commented-out') as HTMLInputElement | null;
      if (commentedOut)
        commentedOut.style.display = 'revert';
      const details = elem.closest('details') as HTMLInputElement | null;
      if (details)
        details.setAttribute("open", "");
      if (commentedOut || details)
        elem.scrollIntoView();
    }
  }
}

export { };
