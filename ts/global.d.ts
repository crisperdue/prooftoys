// Declarations file to cut down on complaints from Typescript.

interface Window {
  _paq: Array;
  $: function;
  proofDisplay: any;
  proofEditor: any;
  rCounter: number;
  dCounter: number;
  idCount: number;
  Numtest: function;
  Rtest: function;
  Tval: any;
  clipboardData: any;
  tippy;
  noTooltipster: any;
  noProofScripts: any;
}

interface HTMLElement {
  onclick: function;
  oninsert: function;
  handleResize: function;
}

interface Object {
  $$: string;
}

interface Error {
  /** Specific step causing a problem */
  step: any;
  /** Array of steps before problem in decodeSteps */
  steps: any[];
  from: any;
}

interface Function {
  done: boolean;
}

interface Promise {
  mq: any;
  id: any;
  canceled: any;
}

interface Console {
  profile(name: string);
  profileEnd();
}
