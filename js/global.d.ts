// Declarations file to cut down on complaints from Typescript.

interface Window {
  _paq: Array;
  $: function;
  proofDisplay: any;
  proofEditor: any;
  rCounter: number;
  dCounter: number;
  Numtest: function;
  Tval: any;
}

interface Element {
  onclick: function;
  handleResize: function;
}

interface Object {
  $$: string;
}
