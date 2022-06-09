export type Content = HTMLElement | string | Content[] | undefined;

const add = (element: HTMLElement, child: Content) => {
  if (typeof child === "string") {
    element.appendChild(document.createTextNode(child.toString()));
  } else if (child instanceof Array) {
    child.forEach((x) => add(element, x));
  } else if (child === undefined || child === null) {
    return;
  } else {
    element.appendChild(child);
  }
};

type JSXName<T> = string | ((props: T) => Node);
type ElemProps = { [id: string]: string | (() => void) | boolean };

export class JSX {
  static createTextNode(t: string): Node {
    return document.createTextNode(t);
  }

  static createElement<T>(fn: (props: T) => Node, props: T, ...content: Content[]): Node;
  static createElement(name: string, props: ElemProps, ...content: Content[]): Node;
  static createElement<P, T extends JSXName<P>>(
    name: T,
    arg: T extends "string" ? ElemProps : P,
    ...content: Content[]
  ): Node {
    if (typeof name !== "string") {
      return name(arg);
    } else {
      const props = (arg as { [id: string]: string | boolean }) || {};
      let element;
      if (typeof props['xmlns'] === 'string') {
        element = document.createElementNS(props['xmlns'], name);
        console.log(element);
      } else {
        element = document.createElement(name);
      }

      for (let name in props) {
        if (name && props.hasOwnProperty(name)) {
          let value = props[name];
          if (typeof(value) === 'function') {
            const id: string = (Math.random() + 1).toString(36);
            (window as any)[id] = value;
            element.setAttribute(name, `window['${id}']()`);
          } else if (value === true) {
            element.setAttribute(name, name);
          } else if (value !== false && value != null) {
            element.setAttribute(name, value.toString());
          }
        }
      }

      for (let i = 0; i < content.length; i++) {
        add(element, content[i]);
      }
      return element;
    }
  }
}

export default JSX;
