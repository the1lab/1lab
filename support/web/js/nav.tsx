import { JSX, Content } from "./lib/jsx";

let fontSizeDisplay: HTMLElement;

function fontSize(): number {
  return Math.round(Number.parseFloat(getComputedStyle(document.body, null).getPropertyValue("font-size")) * 3/4);
}

const makeFontSmaller = () => {
  document.body.style.setProperty("font-size", `${fontSize() - 1}pt`);
  fontSizeDisplay.innerText = `${fontSize()}pt`
}

const makeFontBigger = () => {
  document.body.style.setProperty("font-size", `${fontSize() + 1}pt`);
  fontSizeDisplay.innerText = `${fontSize()}pt`
}

document.addEventListener("DOMContentLoaded", () => {
  const el = document.getElementById("article-nav-link");
  if (el === null || !(el instanceof HTMLAnchorElement)) return;
  el.removeAttribute("href");

  const nav = document.getElementById("article-nav");
  if (nav === null) return;

  el.addEventListener("click", () => {
    nav.classList.toggle("expanded");
  });

  const toggleSans = document.getElementById("toggle-sans-serif");
  const toggleSerif = document.getElementById("toggle-serif");

  toggleSans?.addEventListener("click", () => {
    document.body.classList.add("sans-serif");
    window.localStorage.setItem("1lab.serif_font", "hidden");
  });

  toggleSerif?.addEventListener("click", () => {
    document.body.classList.remove("sans-serif");
    window.localStorage.setItem("1lab.serif_font", "displayed");
  });

  const ctrls = document.getElementById("article-controls");
  ctrls?.appendChild(<div class="font-size-control">
    <div class="button" onclick={makeFontSmaller}>
      <svg xmlns="http://www.w3.org/2000/svg" width="0.85em" height="0.85em" viewBox="0 0 24 24" fill="currentColor">
        <path xmlns="http://www.w3.org/2000/svg" d="M0,13.5v-3h24v3H0z" />
      </svg>
    </div>
    <span id="font-size-display"> {Number.prototype.toString.call(fontSize())}pt </span>
    <div class="button" onclick={makeFontBigger}>
      <svg xmlns="http://www.w3.org/2000/svg" width="0.85em" height="0.85em" viewBox="0 0 24 24" fill="currentColor">
        <path xmlns="http://www.w3.org/2000/svg" d="M24,13.5H13.5V24h-3V13.5H0v-3h10.5V0h3v10.5H24V13.5z" />
      </svg>
    </div>
  </div>);
  fontSizeDisplay = document.getElementById("font-size-display")!;
});

export {};
