// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.


//// General setup for participation in RPC

/**
 * Sets up the worker to handle RPC.  The receiver can be any object
 * with an "actions" property that is a plain object.  Keys in its
 * actions property ("own" properties) become available as values of
 * the "action" property in RPC messages, and the associated function
 * runs to handle the RPC, taking as its argument the message passed
 * in the call to MessageQueue.enqueue.  The function runs with the
 * receiver as "this".
 *
 * Reports the return value of the action function through a "result"
 * property.  Catches errors, and in that case reports the error
 * through an "error" property instead.  If the receiver has an
 * encodeError property, the value is the result of calling that on
 * the thrown value.  Otherwise if the error is an instance of Error,
 * reports the error type name and error message as a plain object
 * with properties "type" and "message", otherwise "?" as the error
 * value.
 */
function initRpc(receiver) {
  self.onmessage = function(event) {
    var wrapper = event.data;
    if (wrapper.channelType === 'RPC') {
      try {
        var id = wrapper.id;
        var message = wrapper.data;
        var action = message.action;
        var actions = receiver.actions;
        if (!actions.hasOwnProperty(action)) {
          throw new Error('Unknown RPC action', action);
        }
        var fn = actions[action].bind(receiver);
        var result = fn(message, wrapper);
        self.postMessage({channelType: 'RPC', id: id, result: result});
      } catch(error) {  // TODO: Consider converting this to catchAll.
        var e = (receiver.encodeError
                 ? receiver.encodeError(error)
                 : error instanceof Error
                 ? {type: error.constructor.name,
                    message: error.message,
                    stack: error.stack}
                 : '?');
        self.postMessage({channelType: 'RPC', id: id, error: e});
      }
    } else if (receiver.handleOther) {
      receiver.handleOther(event);
    } else {
      console.log('Unhandled message', event);
    }
  }
}


//// For testing:

var receiver = {
  actions: {
    ping: function(message) {
      return new Date();
    },
    plus1: function(message) {
      return message.input + 1;
    },
    fail: function(message) {
      throw new Error('Failure!');
    }
  }
};

initRpc(receiver);
