import { Section } from "./items";
import { JSX } from "../lib/jsx";

export const Miscellanea: Section = new Section(<li class="search-header" id="misc-search-header">Search results</li>);
export const InThisPage: Section = new Section(<li class="search-header" id="this-page-search-header">In this page</li>);
export const Settings: Section = new Section(<li class="search-header" id="settings-search-header">Settings</li>);

export const allSections: Section[] = [
  Settings,
  InThisPage,
  Miscellanea,
];
