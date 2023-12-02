export const parseBool = (x: string) => x === 'true';

import { JSX } from "./jsx";
import { type PromptItem } from "../prompt/items";
import { Settings } from "../prompt/sections";

export class Setting<T> {
  private readonly key: string;
  private _value: T;
  private readonly _onChange: ((value: T) => void)[];

  public readonly name: string;

  constructor (name: string, def: T) {
    this.name = name;
    this.key = name.toLowerCase().replace(/[^a-z]/g, '_');
    console.log(this.key);

    let it = window.localStorage.getItem(this.key);
    if (!it) {
      this._value = def
    } else {
      this._value = JSON.parse(it) ?? def;
    };

    this._onChange = [];
  }

  get value(): T {
    return this._value;
  }

  set value(to: T) {
    this._value = to;
    window.localStorage.setItem(this.key, JSON.stringify(to));
    for (const listener of this._onChange) {
      listener(to);
    }
  }

  public toggle(this: Setting<boolean>): boolean {
    return (this.value = !this.value);
  }

  public registerToggle(this: Setting<boolean>, enable?: string, disable?: string): Setting<boolean> {
    const t = this;

    enable  = enable ?? `Enable ${this.name}`;
    disable = disable ?? `Disable ${this.name}`;

    const item: PromptItem = {
      selectors: [this.name, enable, disable],
      priority: 0,
      render(_key, _matched) {
        return <h3 class="search-header"> {t.value ? disable : enable} </h3>;
      },
      activate:  () => {
        t.toggle();
        return 'keep';
      }
    };
    Settings.unshiftPromptItems(item);
    return this;
  }

  onChange(listener: (value: T) => void) {
    this._onChange.push(listener);
    listener(this.value);
  }
}
