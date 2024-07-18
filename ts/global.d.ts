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
}

interface Element {
  onclick: function;
  handleResize: function;
}

interface Object {
  $$: string;
}

interface Error {
  step: any;
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
