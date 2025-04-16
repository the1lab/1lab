import { JSX, type Content } from "./lib/jsx";
import { type Theme, themeSetting, equationSetting, Setting, hiddenCodeSetting, serifFontSetting, justifiedSetting } from "./lib/settings";

// This is pretty evil, but a loose <script> tag assigns these to the
// window object in the HTML template.
const links: { baseUrl: string, source: string } = window as any;

function Button(props: { label: Content, icon?: string, click: ((ev: MouseEvent) => void) | string, ['class']?: string }): HTMLButtonElement {
  const style = `background-image: url('${links.baseUrl}/static/icons/${props.icon}.svg');`;

  const ic: HTMLElement = typeof props.click === 'string' ?
    <a class="icon" style={style} href={props.click} /> :
    <span class="icon" style={style} />;

  const el: HTMLElement =
    <button class={`labelled-button ${props['class'] ?? ''}`}>
      {ic}
      <span class="hover-label">{props.label}</span>
    </button>;

  if (typeof props.click !== 'string') {
    el.addEventListener("click", (ev) => {
      (props.click as any)(ev)
    });
  };

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

interface ToggleProps {
  setting: Setting<boolean>;

  trueLabel:  string;
  falseLabel: string;

  trueIcon:  string;
  falseIcon: string;
}

function ToggleRow({setting, trueLabel, falseLabel, trueIcon, falseIcon }: ToggleProps): HTMLElement {
  const
    onfalse = <Button label={falseLabel} icon={falseIcon} class="button-large" click={() => setting.value = false} />,
    ontrue  = <Button label={trueLabel}  icon={trueIcon}  class="button-large" click={() => setting.value = true} />;

  const go = (v: boolean) => {
    if (v) {
      ontrue.classList.add("active");
      onfalse.classList.remove("active");
    } else {
      onfalse.classList.add("active");
      ontrue.classList.remove("active");
    }
  }

  go(setting.value);
  setting.onChange(go);

  return <ButtonRow>
    {onfalse} {ontrue}
  </ButtonRow>;
}

document.addEventListener("DOMContentLoaded", () => {
  const line = document.querySelector("aside#toc > hr");
  if (!line) return;

  line.parentElement!.insertBefore(
    <div id="controls">
      <Button icon="github" label="Link to source" click={`https://github.com/the1lab/1lab/blob/${links.source}`} />
      <Button icon="all-pages" label="View all pages" click={`${links.baseUrl}/all-pages.html`} />

      <div class="dropdown">
        <Button icon="view-controls" label="View controls" click={(e) => {
          if (!(e.target instanceof HTMLElement)) return;
          e.target.closest("div.dropdown")?.classList.toggle("open");
          e.stopPropagation();
        }}>
        </Button>

        <div class="dropdown-popup">
          <ToggleRow
            setting={serifFontSetting}
            trueLabel="Serif"
            trueIcon="serif"
            falseLabel="Sans"
            falseIcon="view-controls" />

          <hr />

          <ToggleRow
            setting={justifiedSetting}
            trueLabel="Justified"
            trueIcon="justified"
            falseLabel="Left-aligned text"
            falseIcon="raggedright" />

          <Toggle label="Equations"        sync={equationSetting} />
          <Toggle label="Hidden code"      sync={hiddenCodeSetting} />

          <hr />

          <ButtonRow>
            <ThemeButton theme="light"  />
            <ThemeButton theme="dark"   />
            <ThemeButton theme="system" />
          </ButtonRow>
        </div>

      </div>

    </div>, line
  );

  document.addEventListener("click", (e) => {
    if (!(e.target instanceof HTMLElement)) return;
    if (e.target.closest(".dropdown.open")) return;
    Array.from(document.querySelectorAll("div.dropdown.open")).forEach(e => e.classList.remove("open"));
    e.stopPropagation();
  });
});
