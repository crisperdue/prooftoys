// Copyright Crispin Perdue.  All rights reserved.

// prooftoys-scripts.html arranges for dexie.js to be published
// properly.  tsconfig.json ensures that its type info is found.
import { Dexie } from "/js/dexie.js";
import type { Table } from "/js/dexie.js";

export type MyDexie = Dexie & {
  editors: Table<Editor, string>;
  exercises: Table<Exercise, string>;
  prefs: Table<Pref, string>;
};

declare global {
  namespace Toy {
    export var db: MyDexie;
  }
}

interface Editor {
  id: string;
  height?: number;
}

interface Exercise {
  exName: string;
  proofState: string;
}

interface Pref {
  key: string;
  value: string;
}

Toy.db = new Dexie('Prooftoys') as MyDexie;

$(function() {
  Toy.db.version(1).stores({
    prefs: '&key',
    editors: '&id',
    sheets: '&sheetName',
    exercises: '&exName',
  });
  // The lines just above add properties such as prefs to Toy.db.
  Toy.db.prefs.put({key: 'boo', value: 'far'});
});
