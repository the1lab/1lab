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
  if (equations_displayed) {
    window.localStorage.setItem(lsItem, "displayed");
  } else {
    window.localStorage.setItem(lsItem, "hidden");
  }
}

const saveFontDisplay = () => {
  if (serif_font) {
    window.localStorage.setItem(sfItem, "displayed");
  } else {
    window.localStorage.setItem(sfItem, "hidden");
  }
}

window.addEventListener('DOMContentLoaded', () => {
  const buttons = document.querySelectorAll("input.equations");
  const body = document.querySelector("body");

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

  buttons.forEach((button) => {
    if (!button.classList.contains("narrow-only")) {
      button.style = "display: block;";
    }

    if (button.checked !== undefined)
      button.checked = equations_displayed;

    button.onclick = () => {
      equations_displayed = !equations_displayed;

      if (equations_displayed) {
        body.classList.add("show-equations");
      } else {
        body.classList.remove("show-equations");
      }

      saveEqnDisplay();

      buttons.forEach(button => {
        if (button.checked !== undefined)
          button.checked = equations_displayed;

        if (equations_displayed) {
          button.innerText = "Hide equations";
        } else {
          button.innerText = "Show equations";
        }
      })
    };
  });

  const toggleFont = document.getElementById("toggle-fonts");
  toggleFont.checked = serif_font;
  toggleFont.onclick = () => {
    serif_font = toggleFont.checked;
    console.log(serif_font);

    if (serif_font) {
      body.classList.remove("sans-serif");
    } else {
      body.classList.add("sans-serif");
    }

    saveFontDisplay();
  }
});