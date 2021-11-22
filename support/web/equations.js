const lsItem = "1lab.eqn_display";
let equations_displayed = false;
if (window.localStorage.getItem(lsItem) === "displayed") {
  equations_displayed = true;
}

const saveEqnDisplay = () => {
  if (equations_displayed) {
    window.localStorage.setItem(lsItem, "displayed");
  } else {
    window.localStorage.setItem(lsItem, "hidden");
  }
}

window.addEventListener('DOMContentLoaded', () => {
  const buttons = document.querySelectorAll("button.equations");
  const body = document.querySelector("body");

  if (equations_displayed) {
    body.classList.add("show-equations");
  } else {
    body.classList.remove("show-equations");
  }

  buttons.forEach((button) => {
    if (equations_displayed) {
      button.innerText = "Hide equations";
    } else {
      button.innerText = "Show equations";
    }

    if (!button.classList.contains("narrow-only")) {
      button.style = "display: block;";
    }

    button.onclick = () => {
      equations_displayed = !equations_displayed;

      if (equations_displayed) {
        body.classList.add("show-equations");
      } else {
        body.classList.remove("show-equations");
      }

      saveEqnDisplay();

      buttons.forEach(button => {
        if (equations_displayed) {
          button.innerText = "Hide equations";
        } else {
          button.innerText = "Show equations";
        }
      })
    };
  });
});