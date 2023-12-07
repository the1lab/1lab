import { JSX, type Content } from "./lib/jsx";
import { type Theme, themeSetting, equationSetting, Setting, hiddenCodeSetting, footnoteSetting, serifFontSetting } from "./lib/settings";

function Button(props: { label: Content, icon?: string, click: ((ev: MouseEvent) => void), ['class']?: string }): HTMLButtonElement {
  const el: HTMLElement =
    <button class={`labelled-button ${props['class']}`}>
      <span class="icon" style={`background-image: url('/static/icons/${props.icon}.svg');`}></span>
      <span class="hover-label">{props.label}</span>
    </button>;

  el.addEventListener("click", (ev) => props.click(ev));

  return el as HTMLButtonElement;
}

const ButtonRow = () => <div class="button-row" />;

function ThemeButton(props: { theme: Theme }): HTMLElement {
  const elt: HTMLElement =
    <button class={`theme-button theme-button-${props.theme}`}>
      {props.theme[0].toUpperCase() + props.theme.slice(1)}
    </button>;

  themeSetting.onChange((t) => {
    console.log(t, props.theme, t === props.theme);
    t === props.theme ? elt.classList.add("active") : elt.classList.remove("active");
  });

  elt.addEventListener("click", () => themeSetting.value = props.theme);

  return elt;
}

function Toggle(props: { label: string, sync: Setting<boolean> }): HTMLElement {
  const i = <input type="checkbox" /> as HTMLInputElement;

  props.sync.onChange((v) => i.checked = v);
  i.checked = props.sync.value;
  i.addEventListener("click", () => props.sync.toggle());

  return (
    <div class="setting-switch">
      <span>{props.label}</span>
      <label class="switch">
        {i}
        <div class="switch-slider" />
      </label>
    </div>
  );
}

const links: { baseURL: string, source: string } = window as any;

document.addEventListener("DOMContentLoaded", () => {
  const main = document.querySelector("div#post-toc-container");
  if (!main) return;

  const
    sans  = <Button label="Sans" icon="view-controls" class="button-large" click={() => serifFontSetting.value = false} />,
    serif = <Button label="Serif" icon="serif" class="button-large" click={() => serifFontSetting.value = true} />;

  serifFontSetting.onChange((v) => {
    if (v) {
      serif.classList.add("active");
      sans.classList.remove("active");
    } else {
      sans.classList.add("active");
      serif.classList.remove("active");
    }
  });

  main.appendChild(<aside>
    <div id="controls">

      <div class="dropdown">
        <Button icon="view-controls" label="View controls" click={(e) => {
          if (!(e.target instanceof HTMLElement)) return;
          e.target.closest("div.dropdown")?.classList.toggle("open");
          e.stopPropagation();
        }}>
        </Button>

        <div class="dropdown-popup">
          <ButtonRow>
            {sans}
            {serif}
          </ButtonRow>

          <hr />

          {/* <ButtonRow>
            <Button label="Left-aligned text" icon="raggedright" class="button-large" click={console.log} />
            <Button label="Justified text"    icon="justified"   class="button-large" click={console.log} />
            <Button label="Right-aligned text" icon="raggedleft" class="button-large" click={console.log} />
          </ButtonRow> */}

          <hr />

          <Toggle label="Equations"        sync={equationSetting} />
          <Toggle label="Hidden code"      sync={hiddenCodeSetting} />
          <Toggle label="Inline footnotes" sync={footnoteSetting} />

          <hr />

          <ButtonRow>
            <ThemeButton theme="light"  />
            <ThemeButton theme="dark"   />
            <ThemeButton theme="system" />
          </ButtonRow>
        </div>

      </div>

      <Button icon="github" label="Link to source" click={() => window.location.href = `https://github.com/plt-amy/1lab/blob/${links.source}`} />

      <Button icon="home" label="Return to index" click={() => window.location.href = `${links.baseURL}/index.html`} />

      <Button icon="all-pages" label="View all pages" click={() => window.location.href = `${links.baseURL}/all-pages.html`} />
    </div>
  </aside>);

  document.addEventListener("click", (e) => {
    if (!(e.target instanceof HTMLElement)) return;
    if (e.target.closest(".dropdown.open")) return;
    Array.from(document.querySelectorAll("div.dropdown.open")).forEach(e => e.classList.remove("open"));
    e.stopPropagation();
  });
});
