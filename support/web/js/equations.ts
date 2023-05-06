const lsItem = "1lab.eqn_display";
let equations_displayed = false;
if (window.localStorage.getItem(lsItem) === "displayed") {
  equations_displayed = true;
}

const sfItem = "1lab.serif_font";
let serif_font = false;
if (window.localStorage.getItem(sfItem) === "displayed") {
  serif_font = true;
}

const saveEqnDisplay = () => {
  window.localStorage.setItem(lsItem, equations_displayed ? "displayed" : "hidden");
};

const saveFontDisplay = () => {
  window.localStorage.setItem(sfItem, serif_font ? "displayed" : "hidden");
};

window.addEventListener("DOMContentLoaded", () => {
  const buttons: NodeListOf<HTMLInputElement> = document.querySelectorAll("input.equations");
  const body = document.body;

  if (equations_displayed) {
    body.classList.add("show-equations");
  } else {
    body.classList.remove("show-equations");
  }

  if (serif_font) {
    body.classList.remove("sans-serif");
  } else {
    body.classList.add("sans-serif");
  }

  buttons.forEach(button => {
    if (!button.classList.contains("narrow-only")) {
      button.style.display = "block";
    }

    if (button.checked !== undefined) button.checked = equations_displayed;

    button.onclick = () => {
      equations_displayed = !equations_displayed;

      if (equations_displayed) {
        body.classList.add("show-equations");
      } else {
        body.classList.remove("show-equations");
      }

      saveEqnDisplay();

      buttons.forEach((button) => {
        if (button.checked !== undefined) button.checked = equations_displayed;

        if (equations_displayed) {
          button.innerText = "Hide equations";
        } else {
          button.innerText = "Show equations";
        }
      });
    };
  });

  const toggleFont = document.getElementById("toggle-fonts") as HTMLInputElement | null;
  if (toggleFont) {
    toggleFont.checked = serif_font;
    toggleFont.onclick = () => {
      serif_font = toggleFont.checked;

      if (serif_font) {
        body.classList.remove("sans-serif");
      } else {
        body.classList.add("sans-serif");
      }

      saveFontDisplay();
    };
  }

  const showHiddenCode = document.getElementById("sidebar-hidden") as HTMLInputElement | null;
  if (showHiddenCode) {
    showHiddenCode.onchange = () => {
      if (showHiddenCode.checked)
        body.classList.add("show-hidden-code");
      else
        body.classList.remove("show-hidden-code");
    };
  }

  scrollToHash();
});

window.addEventListener("hashchange", scrollToHash);

function scrollToHash() {
  if (window.location.hash != '') {
    const id = window.location.hash.slice(1);
    // #id doesn't work with numerical IDs
    const elem = document.querySelector(`[id="${id}"]`) as HTMLInputElement | null;
    const commentedOut = elem?.closest('.commented-out') as HTMLInputElement | null;
    if (elem && commentedOut) {
      // The element is in a commented-out block: unhide it and scroll to it.
      commentedOut.style.display = 'revert';
      elem.scrollIntoView();
    }
  }
}

export { };
