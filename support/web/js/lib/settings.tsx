const settings: Setting<any>[] = [];

export class Setting<T> {
  private readonly key: string;
  private _value: T;
  private readonly _onChange: ((value: T) => void)[];

  public readonly name: string;

  constructor (name: string, def: T) {
    this.name = name;
    this.key = name.toLowerCase().replace(/[^a-z]/g, '_');

    let it = window.localStorage.getItem(this.key);
    if (!it) {
      this._value = def
    } else {
      this._value = JSON.parse(it) ?? def;
    };

    this._onChange = [];
    settings.push(this);
  }

  get value(): T {
    return this._value;
  }

  set value(to: T) {
    if (this._value === to) return;
    this._value = to;
    window.localStorage.setItem(this.key, JSON.stringify(to));
    for (const listener of this._onChange) {
      listener(to);
    }
  }

  public toggle(this: Setting<boolean>): boolean {
    return (this.value = !this.value);
  }

  public onChange(listener: (value: T) => void) {
    this._onChange.push(listener);
    return this;
  }
}

const clz = document.documentElement.classList;

export type Theme = 'light' | 'dark' | 'system';

export const equationSetting   = new Setting<boolean>("equations",   false)
  .onChange((v) => v ? clz.add("show-equations") : clz.remove("show-equations"));

export const serifFontSetting  = new Setting<boolean>("sans_serif",  false)
  .onChange((v) => v ? clz.remove("sans-serif") : clz.add("sans-serif"));

export const hiddenCodeSetting = new Setting<boolean>("hidden_code", false)
  .onChange((v) => v ? clz.add("show-hidden-code") : clz.remove("show-hidden-code"));

export const footnoteSetting = new Setting<boolean>("inline_footnotes", false)

export const themeSetting = new Setting<Theme>("prefer_theme", 'system').onChange((t) => {
  switch(t) {
    case "light":
      clz.add("light-theme");
      clz.remove("dark-theme");
      break;
    case "dark":
      clz.remove("light-theme");
      clz.add("dark-theme");
      break;
    case "system":
      clz.remove("light-theme", "dark-theme");
      break;
  }
});

export function firstLoad() {
  for (const setting of settings) {
    const v = setting.value;
    for (const l of (setting as any)._onChange) {
      l(v);
    }
  }
}
