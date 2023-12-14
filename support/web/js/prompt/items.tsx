import { Searcher } from "fast-fuzzy";
import { JSX, type Content } from "../lib/jsx";

export type MatchedSpan = { index: number, length: number };
export type ActionAfter = 'keep' | 'close';

export interface PromptItem {
  readonly selectors: string[];
  readonly priority: number;

  readonly onlySearch?: boolean;

  render(key: string, matched?: MatchedSpan): Content;
  activate(): ActionAfter;
}

export const highlight = (original: string, match?: MatchedSpan): Content => {
  if (!match) return original;
  const { index, length } = match;

  if (length == 0) return original;
  if (index == 0 && length == original.length) return <span class="search-match">{original}</span>;

  const out: Array<Content> = [];

  if (index > 0) out.push(original.substring(0, index));
  out.push(<span class="search-match">{original.substring(index, index + length)}</span>);
  out.push(original.substring(index + length));

  return out;
};

export const spanMaybe = (c: Content): Content => {
  if (Array.isArray(c)) {
    return <span>{c}</span>
  } else {
    return c
  };
}

export type PromptItemResult = { item: PromptItem, match: MatchedSpan, original: string };

export interface Context {
  renderItem(it: PromptItemResult): HTMLElement;

  rendered: HTMLElement[];
  pushLate(it: HTMLElement): void;
}

export function isExact(q: string, e: PromptItemResult, sensitive?: boolean): boolean {
  let pred;
  if (sensitive) {
    pred = (v: string) => v === q;
  } else {
    pred = (v: string) => v.toLowerCase() === q.toLowerCase();
  }
  return e.item.selectors.findIndex(pred) >= 0;
}

export function sortPromptItem(search: string) {
  return (p1: PromptItemResult, p2: PromptItemResult): number => {
    let aex = isExact(search, p1, true)
    let bex = isExact(search, p2, true);
    if (aex && !bex) {
      return -1;
    } else if (!aex && bex) {
      return 1;
    }
    if (p1.item.priority === p2.item.priority) {
      return p1.item.selectors[0].localeCompare(p2.item.selectors[0]);
    }
    return p2.item.priority - p1.item.priority;
  }
};

export class Section {
  private readonly entries: PromptItemResult[];
  private readonly searcher: Searcher<PromptItem, { returnMatchData: true }>;

  public readonly header: HTMLElement;
  private sorted: boolean;

  constructor (header: HTMLElement) {
    this.entries  = [];
    this.sorted = true;

    this.searcher = new Searcher([], {
      returnMatchData: true,
      ignoreSymbols: true,
      ignoreCase: true,
      useSellers: true,
      keySelector: (x: PromptItem) => x.selectors,
    });

    this.header = header;
  }

  private sort() {
    if (this.sorted) return;
    this.entries.sort(sortPromptItem(""));
    this.sorted = true;
  }

  public pushPromptItems(...i: PromptItem[]) {
    let res = i.map(x => ({ item: x, match: { index: 0, length: 0 }, original: x.selectors[0] }));

    this.entries.push(...res);
    this.searcher.add(...i);

    this.sorted = false;
  }

  /** Insert a list of {@link PromptItem}s at the end of the {@link promptItems} list.
   *
   * When no search query is present, these will be the shown after any previously-added items. */
  public unshiftPromptItems(...i: PromptItem[]) {
    let res = i.map(x => ({ item: x, match: { index: 0, length: 0 }, original: x.selectors[0] }));

    this.entries.unshift(...res);
    this.searcher.add(...i);

    this.sorted = false;
  }

  public defaultEntries(): PromptItemResult[] {
    this.sort();

    return this.entries.filter((e) => !e.item.onlySearch).slice(0, 512);
  }

  public doSearch(search: string): PromptItemResult[] {
    return this.searcher.search(search);
  }
}
