declare module JSX {
  type Element = HTMLElement;
  interface IntrinsicElements {
    [elemName: string]: any;
  }
}
