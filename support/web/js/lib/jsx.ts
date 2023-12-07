export type Content = HTMLElement | string | Content[] | undefined;

const add = (element: Node, child: Content) => {
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
type ElemProps = { [id: string]: string | boolean };

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
      const elt = name(arg);
      for (const c of content) {
        add(elt, c);
      }
      return elt;
    } else {
      const element = document.createElement(name);
      const props = (arg as { [id: string]: string | boolean }) || {};

      for (const name in props) {
        if (name && props.hasOwnProperty(name)) {
          let value = props[name];
          if (value === true) {
            element.setAttribute(name, name);
          } else if (value !== false && value != null) {
            element.setAttribute(name, value.toString());
          }
        }
      }

      for (const c of content) {
        add(element, c);
      }
      return element;
    }
  }
}

export default JSX;
