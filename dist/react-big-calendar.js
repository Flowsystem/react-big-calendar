;(function(global, factory) {
  typeof exports === 'object' && typeof module !== 'undefined'
    ? factory(
        exports,
        require('react'),
        require('react-dom'),
        require('tty'),
        require('util'),
        require('fs'),
        require('net')
      )
    : typeof define === 'function' && define.amd
    ? define([
        'exports',
        'react',
        'react-dom',
        'tty',
        'util',
        'fs',
        'net',
      ], factory)
    : ((global = global || self),
      factory(
        (global.ReactBigCalendar = {}),
        global.React,
        global.ReactDOM,
        global.tty,
        global.util,
        global.fs,
        global.net
      ))
})(this, function(exports, React, reactDom, tty, util, fs, net) {
  'use strict'

  var React__default = 'default' in React ? React['default'] : React
  var reactDom__default = 'default' in reactDom ? reactDom['default'] : reactDom
  tty = tty && tty.hasOwnProperty('default') ? tty['default'] : tty
  util = util && util.hasOwnProperty('default') ? util['default'] : util
  fs = fs && fs.hasOwnProperty('default') ? fs['default'] : fs
  net = net && net.hasOwnProperty('default') ? net['default'] : net

  function NoopWrapper(props) {
    return props.children
  }

  function _extends() {
    _extends =
      Object.assign ||
      function(target) {
        for (var i = 1; i < arguments.length; i++) {
          var source = arguments[i]

          for (var key in source) {
            if (Object.prototype.hasOwnProperty.call(source, key)) {
              target[key] = source[key]
            }
          }
        }

        return target
      }

    return _extends.apply(this, arguments)
  }

  function _objectWithoutPropertiesLoose(source, excluded) {
    if (source == null) return {}
    var target = {}
    var sourceKeys = Object.keys(source)
    var key, i

    for (i = 0; i < sourceKeys.length; i++) {
      key = sourceKeys[i]
      if (excluded.indexOf(key) >= 0) continue
      target[key] = source[key]
    }

    return target
  }

  function _inheritsLoose(subClass, superClass) {
    subClass.prototype = Object.create(superClass.prototype)
    subClass.prototype.constructor = subClass
    subClass.__proto__ = superClass
  }

  function unwrapExports(x) {
    return x &&
      x.__esModule &&
      Object.prototype.hasOwnProperty.call(x, 'default')
      ? x['default']
      : x
  }

  function createCommonjsModule(fn, module) {
    return (
      (module = { exports: {} }), fn(module, module.exports), module.exports
    )
  }

  var reactIs_production_min = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', { value: !0 })
    var b = 'function' === typeof Symbol && Symbol.for,
      c = b ? Symbol.for('react.element') : 60103,
      d = b ? Symbol.for('react.portal') : 60106,
      e = b ? Symbol.for('react.fragment') : 60107,
      f = b ? Symbol.for('react.strict_mode') : 60108,
      g = b ? Symbol.for('react.profiler') : 60114,
      h = b ? Symbol.for('react.provider') : 60109,
      k = b ? Symbol.for('react.context') : 60110,
      l = b ? Symbol.for('react.async_mode') : 60111,
      m = b ? Symbol.for('react.concurrent_mode') : 60111,
      n = b ? Symbol.for('react.forward_ref') : 60112,
      p = b ? Symbol.for('react.suspense') : 60113,
      q = b ? Symbol.for('react.memo') : 60115,
      r = b ? Symbol.for('react.lazy') : 60116
    function t(a) {
      if ('object' === typeof a && null !== a) {
        var u = a.$$typeof
        switch (u) {
          case c:
            switch (((a = a.type), a)) {
              case l:
              case m:
              case e:
              case g:
              case f:
              case p:
                return a
              default:
                switch (((a = a && a.$$typeof), a)) {
                  case k:
                  case n:
                  case h:
                    return a
                  default:
                    return u
                }
            }
          case r:
          case q:
          case d:
            return u
        }
      }
    }
    function v(a) {
      return t(a) === m
    }
    exports.typeOf = t
    exports.AsyncMode = l
    exports.ConcurrentMode = m
    exports.ContextConsumer = k
    exports.ContextProvider = h
    exports.Element = c
    exports.ForwardRef = n
    exports.Fragment = e
    exports.Lazy = r
    exports.Memo = q
    exports.Portal = d
    exports.Profiler = g
    exports.StrictMode = f
    exports.Suspense = p
    exports.isValidElementType = function(a) {
      return (
        'string' === typeof a ||
        'function' === typeof a ||
        a === e ||
        a === m ||
        a === g ||
        a === f ||
        a === p ||
        ('object' === typeof a &&
          null !== a &&
          (a.$$typeof === r ||
            a.$$typeof === q ||
            a.$$typeof === h ||
            a.$$typeof === k ||
            a.$$typeof === n))
      )
    }
    exports.isAsyncMode = function(a) {
      return v(a) || t(a) === l
    }
    exports.isConcurrentMode = v
    exports.isContextConsumer = function(a) {
      return t(a) === k
    }
    exports.isContextProvider = function(a) {
      return t(a) === h
    }
    exports.isElement = function(a) {
      return 'object' === typeof a && null !== a && a.$$typeof === c
    }
    exports.isForwardRef = function(a) {
      return t(a) === n
    }
    exports.isFragment = function(a) {
      return t(a) === e
    }
    exports.isLazy = function(a) {
      return t(a) === r
    }
    exports.isMemo = function(a) {
      return t(a) === q
    }
    exports.isPortal = function(a) {
      return t(a) === d
    }
    exports.isProfiler = function(a) {
      return t(a) === g
    }
    exports.isStrictMode = function(a) {
      return t(a) === f
    }
    exports.isSuspense = function(a) {
      return t(a) === p
    }
  })

  unwrapExports(reactIs_production_min)
  var reactIs_production_min_1 = reactIs_production_min.typeOf
  var reactIs_production_min_2 = reactIs_production_min.AsyncMode
  var reactIs_production_min_3 = reactIs_production_min.ConcurrentMode
  var reactIs_production_min_4 = reactIs_production_min.ContextConsumer
  var reactIs_production_min_5 = reactIs_production_min.ContextProvider
  var reactIs_production_min_6 = reactIs_production_min.Element
  var reactIs_production_min_7 = reactIs_production_min.ForwardRef
  var reactIs_production_min_8 = reactIs_production_min.Fragment
  var reactIs_production_min_9 = reactIs_production_min.Lazy
  var reactIs_production_min_10 = reactIs_production_min.Memo
  var reactIs_production_min_11 = reactIs_production_min.Portal
  var reactIs_production_min_12 = reactIs_production_min.Profiler
  var reactIs_production_min_13 = reactIs_production_min.StrictMode
  var reactIs_production_min_14 = reactIs_production_min.Suspense
  var reactIs_production_min_15 = reactIs_production_min.isValidElementType
  var reactIs_production_min_16 = reactIs_production_min.isAsyncMode
  var reactIs_production_min_17 = reactIs_production_min.isConcurrentMode
  var reactIs_production_min_18 = reactIs_production_min.isContextConsumer
  var reactIs_production_min_19 = reactIs_production_min.isContextProvider
  var reactIs_production_min_20 = reactIs_production_min.isElement
  var reactIs_production_min_21 = reactIs_production_min.isForwardRef
  var reactIs_production_min_22 = reactIs_production_min.isFragment
  var reactIs_production_min_23 = reactIs_production_min.isLazy
  var reactIs_production_min_24 = reactIs_production_min.isMemo
  var reactIs_production_min_25 = reactIs_production_min.isPortal
  var reactIs_production_min_26 = reactIs_production_min.isProfiler
  var reactIs_production_min_27 = reactIs_production_min.isStrictMode
  var reactIs_production_min_28 = reactIs_production_min.isSuspense

  var reactIs_development = createCommonjsModule(function(module, exports) {
    {
      ;(function() {
        Object.defineProperty(exports, '__esModule', { value: true })

        // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
        // nor polyfill, then a plain number is used for performance.
        var hasSymbol = typeof Symbol === 'function' && Symbol.for

        var REACT_ELEMENT_TYPE = hasSymbol
          ? Symbol.for('react.element')
          : 0xeac7
        var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca
        var REACT_FRAGMENT_TYPE = hasSymbol
          ? Symbol.for('react.fragment')
          : 0xeacb
        var REACT_STRICT_MODE_TYPE = hasSymbol
          ? Symbol.for('react.strict_mode')
          : 0xeacc
        var REACT_PROFILER_TYPE = hasSymbol
          ? Symbol.for('react.profiler')
          : 0xead2
        var REACT_PROVIDER_TYPE = hasSymbol
          ? Symbol.for('react.provider')
          : 0xeacd
        var REACT_CONTEXT_TYPE = hasSymbol
          ? Symbol.for('react.context')
          : 0xeace
        var REACT_ASYNC_MODE_TYPE = hasSymbol
          ? Symbol.for('react.async_mode')
          : 0xeacf
        var REACT_CONCURRENT_MODE_TYPE = hasSymbol
          ? Symbol.for('react.concurrent_mode')
          : 0xeacf
        var REACT_FORWARD_REF_TYPE = hasSymbol
          ? Symbol.for('react.forward_ref')
          : 0xead0
        var REACT_SUSPENSE_TYPE = hasSymbol
          ? Symbol.for('react.suspense')
          : 0xead1
        var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3
        var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4

        function isValidElementType(type) {
          return (
            typeof type === 'string' ||
            typeof type === 'function' ||
            // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
            type === REACT_FRAGMENT_TYPE ||
            type === REACT_CONCURRENT_MODE_TYPE ||
            type === REACT_PROFILER_TYPE ||
            type === REACT_STRICT_MODE_TYPE ||
            type === REACT_SUSPENSE_TYPE ||
            (typeof type === 'object' &&
              type !== null &&
              (type.$$typeof === REACT_LAZY_TYPE ||
                type.$$typeof === REACT_MEMO_TYPE ||
                type.$$typeof === REACT_PROVIDER_TYPE ||
                type.$$typeof === REACT_CONTEXT_TYPE ||
                type.$$typeof === REACT_FORWARD_REF_TYPE))
          )
        }

        /**
         * Forked from fbjs/warning:
         * https://github.com/facebook/fbjs/blob/e66ba20ad5be433eb54423f2b097d829324d9de6/packages/fbjs/src/__forks__/warning.js
         *
         * Only change is we use console.warn instead of console.error,
         * and do nothing when 'console' is not supported.
         * This really simplifies the code.
         * ---
         * Similar to invariant but only logs a warning if the condition is not met.
         * This can be used to log issues in development environments in critical
         * paths. Removing the logging code for production environments will keep the
         * same logic and follow the same code paths.
         */

        var lowPriorityWarning = function() {}

        {
          var printWarning = function(format) {
            for (
              var _len = arguments.length,
                args = Array(_len > 1 ? _len - 1 : 0),
                _key = 1;
              _key < _len;
              _key++
            ) {
              args[_key - 1] = arguments[_key]
            }

            var argIndex = 0
            var message =
              'Warning: ' +
              format.replace(/%s/g, function() {
                return args[argIndex++]
              })
            if (typeof console !== 'undefined') {
              console.warn(message)
            }
            try {
              // --- Welcome to debugging React ---
              // This error was thrown as a convenience so that you can use this stack
              // to find the callsite that caused this warning to fire.
              throw new Error(message)
            } catch (x) {}
          }

          lowPriorityWarning = function(condition, format) {
            if (format === undefined) {
              throw new Error(
                '`lowPriorityWarning(condition, format, ...args)` requires a warning ' +
                  'message argument'
              )
            }
            if (!condition) {
              for (
                var _len2 = arguments.length,
                  args = Array(_len2 > 2 ? _len2 - 2 : 0),
                  _key2 = 2;
                _key2 < _len2;
                _key2++
              ) {
                args[_key2 - 2] = arguments[_key2]
              }

              printWarning.apply(undefined, [format].concat(args))
            }
          }
        }

        var lowPriorityWarning$1 = lowPriorityWarning

        function typeOf(object) {
          if (typeof object === 'object' && object !== null) {
            var $$typeof = object.$$typeof
            switch ($$typeof) {
              case REACT_ELEMENT_TYPE:
                var type = object.type

                switch (type) {
                  case REACT_ASYNC_MODE_TYPE:
                  case REACT_CONCURRENT_MODE_TYPE:
                  case REACT_FRAGMENT_TYPE:
                  case REACT_PROFILER_TYPE:
                  case REACT_STRICT_MODE_TYPE:
                  case REACT_SUSPENSE_TYPE:
                    return type
                  default:
                    var $$typeofType = type && type.$$typeof

                    switch ($$typeofType) {
                      case REACT_CONTEXT_TYPE:
                      case REACT_FORWARD_REF_TYPE:
                      case REACT_PROVIDER_TYPE:
                        return $$typeofType
                      default:
                        return $$typeof
                    }
                }
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PORTAL_TYPE:
                return $$typeof
            }
          }

          return undefined
        }

        // AsyncMode is deprecated along with isAsyncMode
        var AsyncMode = REACT_ASYNC_MODE_TYPE
        var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE
        var ContextConsumer = REACT_CONTEXT_TYPE
        var ContextProvider = REACT_PROVIDER_TYPE
        var Element = REACT_ELEMENT_TYPE
        var ForwardRef = REACT_FORWARD_REF_TYPE
        var Fragment = REACT_FRAGMENT_TYPE
        var Lazy = REACT_LAZY_TYPE
        var Memo = REACT_MEMO_TYPE
        var Portal = REACT_PORTAL_TYPE
        var Profiler = REACT_PROFILER_TYPE
        var StrictMode = REACT_STRICT_MODE_TYPE
        var Suspense = REACT_SUSPENSE_TYPE

        var hasWarnedAboutDeprecatedIsAsyncMode = false

        // AsyncMode should be deprecated
        function isAsyncMode(object) {
          {
            if (!hasWarnedAboutDeprecatedIsAsyncMode) {
              hasWarnedAboutDeprecatedIsAsyncMode = true
              lowPriorityWarning$1(
                false,
                'The ReactIs.isAsyncMode() alias has been deprecated, ' +
                  'and will be removed in React 17+. Update your code to use ' +
                  'ReactIs.isConcurrentMode() instead. It has the exact same API.'
              )
            }
          }
          return (
            isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE
          )
        }
        function isConcurrentMode(object) {
          return typeOf(object) === REACT_CONCURRENT_MODE_TYPE
        }
        function isContextConsumer(object) {
          return typeOf(object) === REACT_CONTEXT_TYPE
        }
        function isContextProvider(object) {
          return typeOf(object) === REACT_PROVIDER_TYPE
        }
        function isElement(object) {
          return (
            typeof object === 'object' &&
            object !== null &&
            object.$$typeof === REACT_ELEMENT_TYPE
          )
        }
        function isForwardRef(object) {
          return typeOf(object) === REACT_FORWARD_REF_TYPE
        }
        function isFragment(object) {
          return typeOf(object) === REACT_FRAGMENT_TYPE
        }
        function isLazy(object) {
          return typeOf(object) === REACT_LAZY_TYPE
        }
        function isMemo(object) {
          return typeOf(object) === REACT_MEMO_TYPE
        }
        function isPortal(object) {
          return typeOf(object) === REACT_PORTAL_TYPE
        }
        function isProfiler(object) {
          return typeOf(object) === REACT_PROFILER_TYPE
        }
        function isStrictMode(object) {
          return typeOf(object) === REACT_STRICT_MODE_TYPE
        }
        function isSuspense(object) {
          return typeOf(object) === REACT_SUSPENSE_TYPE
        }

        exports.typeOf = typeOf
        exports.AsyncMode = AsyncMode
        exports.ConcurrentMode = ConcurrentMode
        exports.ContextConsumer = ContextConsumer
        exports.ContextProvider = ContextProvider
        exports.Element = Element
        exports.ForwardRef = ForwardRef
        exports.Fragment = Fragment
        exports.Lazy = Lazy
        exports.Memo = Memo
        exports.Portal = Portal
        exports.Profiler = Profiler
        exports.StrictMode = StrictMode
        exports.Suspense = Suspense
        exports.isValidElementType = isValidElementType
        exports.isAsyncMode = isAsyncMode
        exports.isConcurrentMode = isConcurrentMode
        exports.isContextConsumer = isContextConsumer
        exports.isContextProvider = isContextProvider
        exports.isElement = isElement
        exports.isForwardRef = isForwardRef
        exports.isFragment = isFragment
        exports.isLazy = isLazy
        exports.isMemo = isMemo
        exports.isPortal = isPortal
        exports.isProfiler = isProfiler
        exports.isStrictMode = isStrictMode
        exports.isSuspense = isSuspense
      })()
    }
  })

  unwrapExports(reactIs_development)
  var reactIs_development_1 = reactIs_development.typeOf
  var reactIs_development_2 = reactIs_development.AsyncMode
  var reactIs_development_3 = reactIs_development.ConcurrentMode
  var reactIs_development_4 = reactIs_development.ContextConsumer
  var reactIs_development_5 = reactIs_development.ContextProvider
  var reactIs_development_6 = reactIs_development.Element
  var reactIs_development_7 = reactIs_development.ForwardRef
  var reactIs_development_8 = reactIs_development.Fragment
  var reactIs_development_9 = reactIs_development.Lazy
  var reactIs_development_10 = reactIs_development.Memo
  var reactIs_development_11 = reactIs_development.Portal
  var reactIs_development_12 = reactIs_development.Profiler
  var reactIs_development_13 = reactIs_development.StrictMode
  var reactIs_development_14 = reactIs_development.Suspense
  var reactIs_development_15 = reactIs_development.isValidElementType
  var reactIs_development_16 = reactIs_development.isAsyncMode
  var reactIs_development_17 = reactIs_development.isConcurrentMode
  var reactIs_development_18 = reactIs_development.isContextConsumer
  var reactIs_development_19 = reactIs_development.isContextProvider
  var reactIs_development_20 = reactIs_development.isElement
  var reactIs_development_21 = reactIs_development.isForwardRef
  var reactIs_development_22 = reactIs_development.isFragment
  var reactIs_development_23 = reactIs_development.isLazy
  var reactIs_development_24 = reactIs_development.isMemo
  var reactIs_development_25 = reactIs_development.isPortal
  var reactIs_development_26 = reactIs_development.isProfiler
  var reactIs_development_27 = reactIs_development.isStrictMode
  var reactIs_development_28 = reactIs_development.isSuspense

  var reactIs = createCommonjsModule(function(module) {
    {
      module.exports = reactIs_development
    }
  })

  /*
  object-assign
  (c) Sindre Sorhus
  @license MIT
  */
  /* eslint-disable no-unused-vars */
  var getOwnPropertySymbols = Object.getOwnPropertySymbols
  var hasOwnProperty = Object.prototype.hasOwnProperty
  var propIsEnumerable = Object.prototype.propertyIsEnumerable

  function toObject(val) {
    if (val === null || val === undefined) {
      throw new TypeError(
        'Object.assign cannot be called with null or undefined'
      )
    }

    return Object(val)
  }

  function shouldUseNative() {
    try {
      if (!Object.assign) {
        return false
      }

      // Detect buggy property enumeration order in older V8 versions.

      // https://bugs.chromium.org/p/v8/issues/detail?id=4118
      var test1 = new String('abc') // eslint-disable-line no-new-wrappers
      test1[5] = 'de'
      if (Object.getOwnPropertyNames(test1)[0] === '5') {
        return false
      }

      // https://bugs.chromium.org/p/v8/issues/detail?id=3056
      var test2 = {}
      for (var i = 0; i < 10; i++) {
        test2['_' + String.fromCharCode(i)] = i
      }
      var order2 = Object.getOwnPropertyNames(test2).map(function(n) {
        return test2[n]
      })
      if (order2.join('') !== '0123456789') {
        return false
      }

      // https://bugs.chromium.org/p/v8/issues/detail?id=3056
      var test3 = {}
      'abcdefghijklmnopqrst'.split('').forEach(function(letter) {
        test3[letter] = letter
      })
      if (
        Object.keys(Object.assign({}, test3)).join('') !==
        'abcdefghijklmnopqrst'
      ) {
        return false
      }

      return true
    } catch (err) {
      // We don't expect any of the above to throw, but better to be safe.
      return false
    }
  }

  var objectAssign = shouldUseNative()
    ? Object.assign
    : function(target, source) {
        var from
        var to = toObject(target)
        var symbols

        for (var s = 1; s < arguments.length; s++) {
          from = Object(arguments[s])

          for (var key in from) {
            if (hasOwnProperty.call(from, key)) {
              to[key] = from[key]
            }
          }

          if (getOwnPropertySymbols) {
            symbols = getOwnPropertySymbols(from)
            for (var i = 0; i < symbols.length; i++) {
              if (propIsEnumerable.call(from, symbols[i])) {
                to[symbols[i]] = from[symbols[i]]
              }
            }
          }
        }

        return to
      }

  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED'

  var ReactPropTypesSecret_1 = ReactPropTypesSecret

  var printWarning = function() {}

  {
    var ReactPropTypesSecret$1 = ReactPropTypesSecret_1
    var loggedTypeFailures = {}
    var has = Function.call.bind(Object.prototype.hasOwnProperty)

    printWarning = function(text) {
      var message = 'Warning: ' + text
      if (typeof console !== 'undefined') {
        console.error(message)
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message)
      } catch (x) {}
    }
  }

  /**
   * Assert that the values match with the type specs.
   * Error messages are memorized and will only be shown once.
   *
   * @param {object} typeSpecs Map of name to a ReactPropType
   * @param {object} values Runtime values that need to be type-checked
   * @param {string} location e.g. "prop", "context", "child context"
   * @param {string} componentName Name of the component for error messages.
   * @param {?Function} getStack Returns the component stack.
   * @private
   */
  function checkPropTypes(
    typeSpecs,
    values,
    location,
    componentName,
    getStack
  ) {
    {
      for (var typeSpecName in typeSpecs) {
        if (has(typeSpecs, typeSpecName)) {
          var error
          // Prop type validation may throw. In case they do, we don't want to
          // fail the render phase where it didn't fail before. So we log it.
          // After these have been cleaned up, we'll let them throw.
          try {
            // This is intentionally an invariant that gets caught. It's the same
            // behavior as without this statement except with a better message.
            if (typeof typeSpecs[typeSpecName] !== 'function') {
              var err = Error(
                (componentName || 'React class') +
                  ': ' +
                  location +
                  ' type `' +
                  typeSpecName +
                  '` is invalid; ' +
                  'it must be a function, usually from the `prop-types` package, but received `' +
                  typeof typeSpecs[typeSpecName] +
                  '`.'
              )
              err.name = 'Invariant Violation'
              throw err
            }
            error = typeSpecs[typeSpecName](
              values,
              typeSpecName,
              componentName,
              location,
              null,
              ReactPropTypesSecret$1
            )
          } catch (ex) {
            error = ex
          }
          if (error && !(error instanceof Error)) {
            printWarning(
              (componentName || 'React class') +
                ': type specification of ' +
                location +
                ' `' +
                typeSpecName +
                '` is invalid; the type checker ' +
                'function must return `null` or an `Error` but returned a ' +
                typeof error +
                '. ' +
                'You may have forgotten to pass an argument to the type checker ' +
                'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
                'shape all require an argument).'
            )
          }
          if (
            error instanceof Error &&
            !(error.message in loggedTypeFailures)
          ) {
            // Only monitor this failure once because there tends to be a lot of the
            // same error.
            loggedTypeFailures[error.message] = true

            var stack = getStack ? getStack() : ''

            printWarning(
              'Failed ' +
                location +
                ' type: ' +
                error.message +
                (stack != null ? stack : '')
            )
          }
        }
      }
    }
  }

  /**
   * Resets warning cache when testing.
   *
   * @private
   */
  checkPropTypes.resetWarningCache = function() {
    {
      loggedTypeFailures = {}
    }
  }

  var checkPropTypes_1 = checkPropTypes

  var has$1 = Function.call.bind(Object.prototype.hasOwnProperty)
  var printWarning$1 = function() {}

  {
    printWarning$1 = function(text) {
      var message = 'Warning: ' + text
      if (typeof console !== 'undefined') {
        console.error(message)
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message)
      } catch (x) {}
    }
  }

  function emptyFunctionThatReturnsNull() {
    return null
  }

  var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
    /* global Symbol */
    var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator
    var FAUX_ITERATOR_SYMBOL = '@@iterator' // Before Symbol spec.

    /**
     * Returns the iterator method function contained on the iterable object.
     *
     * Be sure to invoke the function with the iterable as context:
     *
     *     var iteratorFn = getIteratorFn(myIterable);
     *     if (iteratorFn) {
     *       var iterator = iteratorFn.call(myIterable);
     *       ...
     *     }
     *
     * @param {?object} maybeIterable
     * @return {?function}
     */
    function getIteratorFn(maybeIterable) {
      var iteratorFn =
        maybeIterable &&
        ((ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL]) ||
          maybeIterable[FAUX_ITERATOR_SYMBOL])
      if (typeof iteratorFn === 'function') {
        return iteratorFn
      }
    }

    /**
     * Collection of methods that allow declaration and validation of props that are
     * supplied to React components. Example usage:
     *
     *   var Props = require('ReactPropTypes');
     *   var MyArticle = React.createClass({
     *     propTypes: {
     *       // An optional string prop named "description".
     *       description: Props.string,
     *
     *       // A required enum prop named "category".
     *       category: Props.oneOf(['News','Photos']).isRequired,
     *
     *       // A prop named "dialog" that requires an instance of Dialog.
     *       dialog: Props.instanceOf(Dialog).isRequired
     *     },
     *     render: function() { ... }
     *   });
     *
     * A more formal specification of how these methods are used:
     *
     *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
     *   decl := ReactPropTypes.{type}(.isRequired)?
     *
     * Each and every declaration produces a function with the same signature. This
     * allows the creation of custom validation functions. For example:
     *
     *  var MyLink = React.createClass({
     *    propTypes: {
     *      // An optional string or URI prop named "href".
     *      href: function(props, propName, componentName) {
     *        var propValue = props[propName];
     *        if (propValue != null && typeof propValue !== 'string' &&
     *            !(propValue instanceof URI)) {
     *          return new Error(
     *            'Expected a string or an URI for ' + propName + ' in ' +
     *            componentName
     *          );
     *        }
     *      }
     *    },
     *    render: function() {...}
     *  });
     *
     * @internal
     */

    var ANONYMOUS = '<<anonymous>>'

    // Important!
    // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
    var ReactPropTypes = {
      array: createPrimitiveTypeChecker('array'),
      bool: createPrimitiveTypeChecker('boolean'),
      func: createPrimitiveTypeChecker('function'),
      number: createPrimitiveTypeChecker('number'),
      object: createPrimitiveTypeChecker('object'),
      string: createPrimitiveTypeChecker('string'),
      symbol: createPrimitiveTypeChecker('symbol'),

      any: createAnyTypeChecker(),
      arrayOf: createArrayOfTypeChecker,
      element: createElementTypeChecker(),
      elementType: createElementTypeTypeChecker(),
      instanceOf: createInstanceTypeChecker,
      node: createNodeChecker(),
      objectOf: createObjectOfTypeChecker,
      oneOf: createEnumTypeChecker,
      oneOfType: createUnionTypeChecker,
      shape: createShapeTypeChecker,
      exact: createStrictShapeTypeChecker,
    }

    /**
     * inlined Object.is polyfill to avoid requiring consumers ship their own
     * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
     */
    /*eslint-disable no-self-compare*/
    function is(x, y) {
      // SameValue algorithm
      if (x === y) {
        // Steps 1-5, 7-10
        // Steps 6.b-6.e: +0 != -0
        return x !== 0 || 1 / x === 1 / y
      } else {
        // Step 6.a: NaN == NaN
        return x !== x && y !== y
      }
    }
    /*eslint-enable no-self-compare*/

    /**
     * We use an Error-like object for backward compatibility as people may call
     * PropTypes directly and inspect their output. However, we don't use real
     * Errors anymore. We don't inspect their stack anyway, and creating them
     * is prohibitively expensive if they are created too often, such as what
     * happens in oneOfType() for any type before the one that matched.
     */
    function PropTypeError(message) {
      this.message = message
      this.stack = ''
    }
    // Make `instanceof Error` still work for returned errors.
    PropTypeError.prototype = Error.prototype

    function createChainableTypeChecker(validate) {
      {
        var manualPropTypeCallCache = {}
        var manualPropTypeWarningCount = 0
      }
      function checkType(
        isRequired,
        props,
        propName,
        componentName,
        location,
        propFullName,
        secret
      ) {
        componentName = componentName || ANONYMOUS
        propFullName = propFullName || propName

        if (secret !== ReactPropTypesSecret_1) {
          if (throwOnDirectAccess) {
            // New behavior only for users of `prop-types` package
            var err = new Error(
              'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
                'Use `PropTypes.checkPropTypes()` to call them. ' +
                'Read more at http://fb.me/use-check-prop-types'
            )
            err.name = 'Invariant Violation'
            throw err
          } else if (typeof console !== 'undefined') {
            // Old behavior for people using React.PropTypes
            var cacheKey = componentName + ':' + propName
            if (
              !manualPropTypeCallCache[cacheKey] &&
              // Avoid spamming the console because they are often not actionable except for lib authors
              manualPropTypeWarningCount < 3
            ) {
              printWarning$1(
                'You are manually calling a React.PropTypes validation ' +
                  'function for the `' +
                  propFullName +
                  '` prop on `' +
                  componentName +
                  '`. This is deprecated ' +
                  'and will throw in the standalone `prop-types` package. ' +
                  'You may be seeing this warning due to a third-party PropTypes ' +
                  'library. See https://fb.me/react-warning-dont-call-proptypes ' +
                  'for details.'
              )
              manualPropTypeCallCache[cacheKey] = true
              manualPropTypeWarningCount++
            }
          }
        }
        if (props[propName] == null) {
          if (isRequired) {
            if (props[propName] === null) {
              return new PropTypeError(
                'The ' +
                  location +
                  ' `' +
                  propFullName +
                  '` is marked as required ' +
                  ('in `' + componentName + '`, but its value is `null`.')
              )
            }
            return new PropTypeError(
              'The ' +
                location +
                ' `' +
                propFullName +
                '` is marked as required in ' +
                ('`' + componentName + '`, but its value is `undefined`.')
            )
          }
          return null
        } else {
          return validate(
            props,
            propName,
            componentName,
            location,
            propFullName
          )
        }
      }

      var chainedCheckType = checkType.bind(null, false)
      chainedCheckType.isRequired = checkType.bind(null, true)

      return chainedCheckType
    }

    function createPrimitiveTypeChecker(expectedType) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName,
        secret
      ) {
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== expectedType) {
          // `propValue` being instance of, say, date/regexp, pass the 'object'
          // check, but we can offer a more precise error message here rather than
          // 'of type `object`'.
          var preciseType = getPreciseType(propValue)

          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                preciseType +
                '` supplied to `' +
                componentName +
                '`, expected ') +
              ('`' + expectedType + '`.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createAnyTypeChecker() {
      return createChainableTypeChecker(emptyFunctionThatReturnsNull)
    }

    function createArrayOfTypeChecker(typeChecker) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError(
            'Property `' +
              propFullName +
              '` of component `' +
              componentName +
              '` has invalid PropType notation inside arrayOf.'
          )
        }
        var propValue = props[propName]
        if (!Array.isArray(propValue)) {
          var propType = getPropType(propValue)
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected an array.')
          )
        }
        for (var i = 0; i < propValue.length; i++) {
          var error = typeChecker(
            propValue,
            i,
            componentName,
            location,
            propFullName + '[' + i + ']',
            ReactPropTypesSecret_1
          )
          if (error instanceof Error) {
            return error
          }
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createElementTypeChecker() {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        if (!isValidElement(propValue)) {
          var propType = getPropType(propValue)
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected a single ReactElement.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createElementTypeTypeChecker() {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        if (!reactIs.isValidElementType(propValue)) {
          var propType = getPropType(propValue)
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected a single ReactElement type.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createInstanceTypeChecker(expectedClass) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (!(props[propName] instanceof expectedClass)) {
          var expectedClassName = expectedClass.name || ANONYMOUS
          var actualClassName = getClassName(props[propName])
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                actualClassName +
                '` supplied to `' +
                componentName +
                '`, expected ') +
              ('instance of `' + expectedClassName + '`.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createEnumTypeChecker(expectedValues) {
      if (!Array.isArray(expectedValues)) {
        {
          if (arguments.length > 1) {
            printWarning$1(
              'Invalid arguments supplied to oneOf, expected an array, got ' +
                arguments.length +
                ' arguments. ' +
                'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
            )
          } else {
            printWarning$1(
              'Invalid argument supplied to oneOf, expected an array.'
            )
          }
        }
        return emptyFunctionThatReturnsNull
      }

      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        for (var i = 0; i < expectedValues.length; i++) {
          if (is(propValue, expectedValues[i])) {
            return null
          }
        }

        var valuesString = JSON.stringify(expectedValues, function replacer(
          key,
          value
        ) {
          var type = getPreciseType(value)
          if (type === 'symbol') {
            return String(value)
          }
          return value
        })
        return new PropTypeError(
          'Invalid ' +
            location +
            ' `' +
            propFullName +
            '` of value `' +
            String(propValue) +
            '` ' +
            ('supplied to `' +
              componentName +
              '`, expected one of ' +
              valuesString +
              '.')
        )
      }
      return createChainableTypeChecker(validate)
    }

    function createObjectOfTypeChecker(typeChecker) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError(
            'Property `' +
              propFullName +
              '` of component `' +
              componentName +
              '` has invalid PropType notation inside objectOf.'
          )
        }
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== 'object') {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected an object.')
          )
        }
        for (var key in propValue) {
          if (has$1(propValue, key)) {
            var error = typeChecker(
              propValue,
              key,
              componentName,
              location,
              propFullName + '.' + key,
              ReactPropTypesSecret_1
            )
            if (error instanceof Error) {
              return error
            }
          }
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createUnionTypeChecker(arrayOfTypeCheckers) {
      if (!Array.isArray(arrayOfTypeCheckers)) {
        printWarning$1(
          'Invalid argument supplied to oneOfType, expected an instance of array.'
        )
        return emptyFunctionThatReturnsNull
      }

      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i]
        if (typeof checker !== 'function') {
          printWarning$1(
            'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
              'received ' +
              getPostfixForTypeWarning(checker) +
              ' at index ' +
              i +
              '.'
          )
          return emptyFunctionThatReturnsNull
        }
      }

      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
          var checker = arrayOfTypeCheckers[i]
          if (
            checker(
              props,
              propName,
              componentName,
              location,
              propFullName,
              ReactPropTypesSecret_1
            ) == null
          ) {
            return null
          }
        }

        return new PropTypeError(
          'Invalid ' +
            location +
            ' `' +
            propFullName +
            '` supplied to ' +
            ('`' + componentName + '`.')
        )
      }
      return createChainableTypeChecker(validate)
    }

    function createNodeChecker() {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (!isNode(props[propName])) {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` supplied to ' +
              ('`' + componentName + '`, expected a ReactNode.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createShapeTypeChecker(shapeTypes) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== 'object') {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type `' +
              propType +
              '` ' +
              ('supplied to `' + componentName + '`, expected `object`.')
          )
        }
        for (var key in shapeTypes) {
          var checker = shapeTypes[key]
          if (!checker) {
            continue
          }
          var error = checker(
            propValue,
            key,
            componentName,
            location,
            propFullName + '.' + key,
            ReactPropTypesSecret_1
          )
          if (error) {
            return error
          }
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createStrictShapeTypeChecker(shapeTypes) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== 'object') {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type `' +
              propType +
              '` ' +
              ('supplied to `' + componentName + '`, expected `object`.')
          )
        }
        // We need to check all keys in case some are required but missing from
        // props.
        var allKeys = objectAssign({}, props[propName], shapeTypes)
        for (var key in allKeys) {
          var checker = shapeTypes[key]
          if (!checker) {
            return new PropTypeError(
              'Invalid ' +
                location +
                ' `' +
                propFullName +
                '` key `' +
                key +
                '` supplied to `' +
                componentName +
                '`.' +
                '\nBad object: ' +
                JSON.stringify(props[propName], null, '  ') +
                '\nValid keys: ' +
                JSON.stringify(Object.keys(shapeTypes), null, '  ')
            )
          }
          var error = checker(
            propValue,
            key,
            componentName,
            location,
            propFullName + '.' + key,
            ReactPropTypesSecret_1
          )
          if (error) {
            return error
          }
        }
        return null
      }

      return createChainableTypeChecker(validate)
    }

    function isNode(propValue) {
      switch (typeof propValue) {
        case 'number':
        case 'string':
        case 'undefined':
          return true
        case 'boolean':
          return !propValue
        case 'object':
          if (Array.isArray(propValue)) {
            return propValue.every(isNode)
          }
          if (propValue === null || isValidElement(propValue)) {
            return true
          }

          var iteratorFn = getIteratorFn(propValue)
          if (iteratorFn) {
            var iterator = iteratorFn.call(propValue)
            var step
            if (iteratorFn !== propValue.entries) {
              while (!(step = iterator.next()).done) {
                if (!isNode(step.value)) {
                  return false
                }
              }
            } else {
              // Iterator will provide entry [k,v] tuples rather than values.
              while (!(step = iterator.next()).done) {
                var entry = step.value
                if (entry) {
                  if (!isNode(entry[1])) {
                    return false
                  }
                }
              }
            }
          } else {
            return false
          }

          return true
        default:
          return false
      }
    }

    function isSymbol(propType, propValue) {
      // Native Symbol.
      if (propType === 'symbol') {
        return true
      }

      // falsy value can't be a Symbol
      if (!propValue) {
        return false
      }

      // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
      if (propValue['@@toStringTag'] === 'Symbol') {
        return true
      }

      // Fallback for non-spec compliant Symbols which are polyfilled.
      if (typeof Symbol === 'function' && propValue instanceof Symbol) {
        return true
      }

      return false
    }

    // Equivalent of `typeof` but with special handling for array and regexp.
    function getPropType(propValue) {
      var propType = typeof propValue
      if (Array.isArray(propValue)) {
        return 'array'
      }
      if (propValue instanceof RegExp) {
        // Old webkits (at least until Android 4.0) return 'function' rather than
        // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
        // passes PropTypes.object.
        return 'object'
      }
      if (isSymbol(propType, propValue)) {
        return 'symbol'
      }
      return propType
    }

    // This handles more types than `getPropType`. Only used for error messages.
    // See `createPrimitiveTypeChecker`.
    function getPreciseType(propValue) {
      if (typeof propValue === 'undefined' || propValue === null) {
        return '' + propValue
      }
      var propType = getPropType(propValue)
      if (propType === 'object') {
        if (propValue instanceof Date) {
          return 'date'
        } else if (propValue instanceof RegExp) {
          return 'regexp'
        }
      }
      return propType
    }

    // Returns a string that is postfixed to a warning about an invalid type.
    // For example, "undefined" or "of type array"
    function getPostfixForTypeWarning(value) {
      var type = getPreciseType(value)
      switch (type) {
        case 'array':
        case 'object':
          return 'an ' + type
        case 'boolean':
        case 'date':
        case 'regexp':
          return 'a ' + type
        default:
          return type
      }
    }

    // Returns class name of the object, if any.
    function getClassName(propValue) {
      if (!propValue.constructor || !propValue.constructor.name) {
        return ANONYMOUS
      }
      return propValue.constructor.name
    }

    ReactPropTypes.checkPropTypes = checkPropTypes_1
    ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache
    ReactPropTypes.PropTypes = ReactPropTypes

    return ReactPropTypes
  }

  var propTypes = createCommonjsModule(function(module) {
    /**
     * Copyright (c) 2013-present, Facebook, Inc.
     *
     * This source code is licensed under the MIT license found in the
     * LICENSE file in the root directory of this source tree.
     */

    {
      var ReactIs = reactIs

      // By explicitly using `prop-types` you are opting into new development behavior.
      // http://fb.me/prop-types-in-prod
      var throwOnDirectAccess = true
      module.exports = factoryWithTypeCheckers(
        ReactIs.isElement,
        throwOnDirectAccess
      )
    }
  })

  function _extends$1() {
    _extends$1 =
      Object.assign ||
      function(target) {
        for (var i = 1; i < arguments.length; i++) {
          var source = arguments[i]

          for (var key in source) {
            if (Object.prototype.hasOwnProperty.call(source, key)) {
              target[key] = source[key]
            }
          }
        }

        return target
      }

    return _extends$1.apply(this, arguments)
  }

  function _objectWithoutPropertiesLoose$1(source, excluded) {
    if (source == null) return {}
    var target = {}
    var sourceKeys = Object.keys(source)
    var key, i

    for (i = 0; i < sourceKeys.length; i++) {
      key = sourceKeys[i]
      if (excluded.indexOf(key) >= 0) continue
      target[key] = source[key]
    }

    return target
  }

  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  var invariant = function(condition, format, a, b, c, d, e, f) {
    {
      if (format === undefined) {
        throw new Error('invariant requires an error message argument')
      }
    }

    if (!condition) {
      var error
      if (format === undefined) {
        error = new Error(
          'Minified exception occurred; use the non-minified dev environment ' +
            'for the full error message and additional helpful warnings.'
        )
      } else {
        var args = [a, b, c, d, e, f]
        var argIndex = 0
        error = new Error(
          format.replace(/%s/g, function() {
            return args[argIndex++]
          })
        )
        error.name = 'Invariant Violation'
      }

      error.framesToPop = 1 // we don't care about invariant's own frame
      throw error
    }
  }

  var invariant_1 = invariant

  var noop = function noop() {}

  function readOnlyPropType(handler, name) {
    return function(props, propName) {
      if (props[propName] !== undefined) {
        if (!props[handler]) {
          return new Error(
            'You have provided a `' +
              propName +
              '` prop to `' +
              name +
              '` ' +
              ('without an `' +
                handler +
                '` handler prop. This will render a read-only field. ') +
              ('If the field should be mutable use `' +
                defaultKey(propName) +
                '`. ') +
              ('Otherwise, set `' + handler + '`.')
          )
        }
      }
    }
  }

  function uncontrolledPropTypes(controlledValues, displayName) {
    var propTypes = {}
    Object.keys(controlledValues).forEach(function(prop) {
      // add default propTypes for folks that use runtime checks
      propTypes[defaultKey(prop)] = noop

      {
        var handler = controlledValues[prop]
        !(typeof handler === 'string' && handler.trim().length)
          ? invariant_1(
              false,
              'Uncontrollable - [%s]: the prop `%s` needs a valid handler key name in order to make it uncontrollable',
              displayName,
              prop
            )
          : void 0
        propTypes[prop] = readOnlyPropType(handler, displayName)
      }
    })
    return propTypes
  }
  function isProp(props, prop) {
    return props[prop] !== undefined
  }
  function defaultKey(key) {
    return 'default' + key.charAt(0).toUpperCase() + key.substr(1)
  }
  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   * All rights reserved.
   *
   * This source code is licensed under the BSD-style license found in the
   * LICENSE file in the root directory of this source tree. An additional grant
   * of patent rights can be found in the PATENTS file in the same directory.
   */

  function canAcceptRef(component) {
    return (
      !!component &&
      (typeof component !== 'function' ||
        (component.prototype && component.prototype.isReactComponent))
    )
  }

  function _inheritsLoose$1(subClass, superClass) {
    subClass.prototype = Object.create(superClass.prototype)
    subClass.prototype.constructor = subClass
    subClass.__proto__ = superClass
  }

  function uncontrollable(Component, controlledValues, methods) {
    if (methods === void 0) {
      methods = []
    }

    var displayName = Component.displayName || Component.name || 'Component'
    var canAcceptRef$1 = canAcceptRef(Component)
    var controlledProps = Object.keys(controlledValues)
    var PROPS_TO_OMIT = controlledProps.map(defaultKey)
    !(canAcceptRef$1 || !methods.length)
      ? invariant_1(
          false,
          '[uncontrollable] stateless function components cannot pass through methods ' +
            'because they have no associated instances. Check component: ' +
            displayName +
            ', ' +
            'attempting to pass through methods: ' +
            methods.join(', ')
        )
      : void 0

    var UncontrolledComponent =
      /*#__PURE__*/
      (function(_React$Component) {
        _inheritsLoose$1(UncontrolledComponent, _React$Component)

        function UncontrolledComponent() {
          var _this

          for (
            var _len = arguments.length, args = new Array(_len), _key = 0;
            _key < _len;
            _key++
          ) {
            args[_key] = arguments[_key]
          }

          _this =
            _React$Component.call.apply(
              _React$Component,
              [this].concat(args)
            ) || this
          _this.handlers = Object.create(null)
          controlledProps.forEach(function(propName) {
            var handlerName = controlledValues[propName]

            var handleChange = function handleChange(value) {
              if (_this.props[handlerName]) {
                var _this$props

                _this._notifying = true

                for (
                  var _len2 = arguments.length,
                    args = new Array(_len2 > 1 ? _len2 - 1 : 0),
                    _key2 = 1;
                  _key2 < _len2;
                  _key2++
                ) {
                  args[_key2 - 1] = arguments[_key2]
                }

                ;(_this$props = _this.props)[handlerName].apply(
                  _this$props,
                  [value].concat(args)
                )

                _this._notifying = false
              }

              _this._values[propName] = value
              if (!_this.unmounted) _this.forceUpdate()
            }

            _this.handlers[handlerName] = handleChange
          })
          if (methods.length)
            _this.attachRef = function(ref) {
              _this.inner = ref
            }
          return _this
        }

        var _proto = UncontrolledComponent.prototype

        _proto.shouldComponentUpdate = function shouldComponentUpdate() {
          //let the forceUpdate trigger the update
          return !this._notifying
        }

        _proto.componentWillMount = function componentWillMount() {
          var _this2 = this

          var props = this.props
          this._values = Object.create(null)
          controlledProps.forEach(function(key) {
            _this2._values[key] = props[defaultKey(key)]
          })
        }

        _proto.componentWillReceiveProps = function componentWillReceiveProps(
          nextProps
        ) {
          var _this3 = this

          var props = this.props
          controlledProps.forEach(function(key) {
            /**
             * If a prop switches from controlled to Uncontrolled
             * reset its value to the defaultValue
             */
            if (!isProp(nextProps, key) && isProp(props, key)) {
              _this3._values[key] = nextProps[defaultKey(key)]
            }
          })
        }

        _proto.componentWillUnmount = function componentWillUnmount() {
          this.unmounted = true
        }

        _proto.render = function render() {
          var _this4 = this

          var _this$props2 = this.props,
            innerRef = _this$props2.innerRef,
            props = _objectWithoutPropertiesLoose$1(_this$props2, ['innerRef'])

          PROPS_TO_OMIT.forEach(function(prop) {
            delete props[prop]
          })
          var newProps = {}
          controlledProps.forEach(function(propName) {
            var propValue = _this4.props[propName]
            newProps[propName] =
              propValue !== undefined ? propValue : _this4._values[propName]
          })
          return React__default.createElement(
            Component,
            _extends$1({}, props, newProps, this.handlers, {
              ref: innerRef || this.attachRef,
            })
          )
        }

        return UncontrolledComponent
      })(React__default.Component)

    UncontrolledComponent.displayName = 'Uncontrolled(' + displayName + ')'
    UncontrolledComponent.propTypes = _extends$1(
      {
        innerRef: function innerRef() {},
      },
      uncontrolledPropTypes(controlledValues, displayName)
    )
    methods.forEach(function(method) {
      UncontrolledComponent.prototype[method] = function $proxiedMethod() {
        var _this$inner

        return (_this$inner = this.inner)[method].apply(_this$inner, arguments)
      }
    })
    var WrappedComponent = UncontrolledComponent

    if (React__default.forwardRef) {
      WrappedComponent = React__default.forwardRef(function(props, ref) {
        return React__default.createElement(
          UncontrolledComponent,
          _extends$1({}, props, {
            innerRef: ref,
          })
        )
      })
      WrappedComponent.propTypes = UncontrolledComponent.propTypes
    }

    WrappedComponent.ControlledComponent = Component
    /**
     * useful when wrapping a Component and you want to control
     * everything
     */

    WrappedComponent.deferControlTo = function(
      newComponent,
      additions,
      nextMethods
    ) {
      if (additions === void 0) {
        additions = {}
      }

      return uncontrollable(
        newComponent,
        _extends$1({}, controlledValues, additions),
        nextMethods
      )
    }

    return WrappedComponent
  }

  function toVal(mix) {
    var k,
      y,
      str = ''
    if (mix) {
      if (typeof mix === 'object') {
        if (!!mix.push) {
          for (k = 0; k < mix.length; k++) {
            if (mix[k] && (y = toVal(mix[k]))) {
              str && (str += ' ')
              str += y
            }
          }
        } else {
          for (k in mix) {
            if (mix[k] && (y = toVal(k))) {
              str && (str += ' ')
              str += y
            }
          }
        }
      } else if (typeof mix !== 'boolean' && !mix.call) {
        str && (str += ' ')
        str += mix
      }
    }
    return str
  }

  function clsx() {
    var i = 0,
      x,
      str = ''
    while (i < arguments.length) {
      if ((x = toVal(arguments[i++]))) {
        str && (str += ' ')
        str += x
      }
    }
    return str
  }

  var navigate = {
    PREVIOUS: 'PREV',
    NEXT: 'NEXT',
    TODAY: 'TODAY',
    DATE: 'DATE',
  }
  var views = {
    MONTH: 'month',
    WEEK: 'week',
    WORK_WEEK: 'work_week',
    DAY: 'day',
    AGENDA: 'agenda',
  }

  var viewNames = Object.keys(views).map(function(k) {
    return views[k]
  })
  var accessor = propTypes.oneOfType([propTypes.string, propTypes.func])
  var dateFormat = propTypes.any
  var dateRangeFormat = propTypes.func
  /**
   * accepts either an array of builtin view names:
   *
   * ```
   * views={['month', 'day', 'agenda']}
   * ```
   *
   * or an object hash of the view name and the component (or boolean for builtin)
   *
   * ```
   * views={{
   *   month: true,
   *   week: false,
   *   workweek: WorkWeekViewComponent,
   * }}
   * ```
   */

  var views$1 = propTypes.oneOfType([
    propTypes.arrayOf(propTypes.oneOf(viewNames)),
    propTypes.objectOf(function(prop, key) {
      var isBuiltinView =
        viewNames.indexOf(key) !== -1 && typeof prop[key] === 'boolean'

      if (isBuiltinView) {
        return null
      } else {
        for (
          var _len = arguments.length,
            args = new Array(_len > 2 ? _len - 2 : 0),
            _key = 2;
          _key < _len;
          _key++
        ) {
          args[_key - 2] = arguments[_key]
        }

        return propTypes.elementType.apply(propTypes, [prop, key].concat(args))
      }
    }),
  ])
  var DayLayoutAlgorithmPropType = propTypes.oneOfType([
    propTypes.oneOf(['overlap', 'no-overlap']),
    propTypes.func,
  ])

  function notify(handler, args) {
    handler && handler.apply(null, [].concat(args))
  }

  var localePropType = propTypes.oneOfType([propTypes.string, propTypes.func])

  function _format(localizer, formatter, value, format, culture) {
    var result =
      typeof format === 'function'
        ? format(value, culture, localizer)
        : formatter.call(localizer, value, format, culture)
    !(result == null || typeof result === 'string')
      ? invariant_1(
          false,
          '`localizer format(..)` must return a string, null, or undefined'
        )
      : void 0
    return result
  }

  var DateLocalizer = function DateLocalizer(spec) {
    var _this = this

    !(typeof spec.format === 'function')
      ? invariant_1(false, 'date localizer `format(..)` must be a function')
      : void 0
    !(typeof spec.firstOfWeek === 'function')
      ? invariant_1(
          false,
          'date localizer `firstOfWeek(..)` must be a function'
        )
      : void 0
    this.propType = spec.propType || localePropType
    this.startOfWeek = spec.firstOfWeek
    this.formats = spec.formats

    this.format = function() {
      for (
        var _len = arguments.length, args = new Array(_len), _key = 0;
        _key < _len;
        _key++
      ) {
        args[_key] = arguments[_key]
      }

      return _format.apply(void 0, [_this, spec.format].concat(args))
    }
  }
  function mergeWithDefaults(localizer, culture, formatOverrides, messages) {
    var formats = _extends({}, localizer.formats, formatOverrides)

    return _extends({}, localizer, {
      messages: messages,
      startOfWeek: function startOfWeek() {
        return localizer.startOfWeek(culture)
      },
      format: function format(value, _format2) {
        return localizer.format(value, formats[_format2] || _format2, culture)
      },
    })
  }

  var defaultMessages = {
    date: 'Date',
    time: 'Time',
    event: 'Event',
    allDay: 'All Day',
    week: 'Week',
    work_week: 'Work Week',
    day: 'Day',
    month: 'Month',
    previous: 'Back',
    next: 'Next',
    yesterday: 'Yesterday',
    tomorrow: 'Tomorrow',
    today: 'Today',
    agenda: 'Agenda',
    noEventsInRange: 'There are no events in this range.',
    showMore: function showMore(total) {
      return '+' + total + ' more'
    },
  }
  function messages(msgs) {
    return _extends({}, defaultMessages, msgs)
  }

  function _assertThisInitialized(self) {
    if (self === void 0) {
      throw new ReferenceError(
        "this hasn't been initialised - super() hasn't been called"
      )
    }

    return self
  }

  var MILI = 'milliseconds',
    SECONDS = 'seconds',
    MINUTES = 'minutes',
    HOURS = 'hours',
    DAY = 'day',
    WEEK = 'week',
    MONTH = 'month',
    YEAR = 'year',
    DECADE = 'decade',
    CENTURY = 'century'

  function add(d, num, unit) {
    d = new Date(d)

    switch (unit) {
      case MILI:
        return milliseconds(d, milliseconds(d) + num)
      case SECONDS:
        return seconds(d, seconds(d) + num)
      case MINUTES:
        return minutes(d, minutes(d) + num)
      case HOURS:
        return hours(d, hours(d) + num)
      case YEAR:
        return year(d, year(d) + num)
      case DAY:
        return date(d, date(d) + num)
      case WEEK:
        return date(d, date(d) + 7 * num)
      case MONTH:
        return monthMath(d, num)
      case DECADE:
        return year(d, year(d) + num * 10)
      case CENTURY:
        return year(d, year(d) + num * 100)
    }

    throw new TypeError('Invalid units: "' + unit + '"')
  }

  function subtract(d, num, unit) {
    return add(d, -num, unit)
  }

  function startOf(d, unit, firstOfWeek) {
    d = new Date(d)

    switch (unit) {
      case CENTURY:
      case DECADE:
      case YEAR:
        d = month(d, 0)
      case MONTH:
        d = date(d, 1)
      case WEEK:
      case DAY:
        d = hours(d, 0)
      case HOURS:
        d = minutes(d, 0)
      case MINUTES:
        d = seconds(d, 0)
      case SECONDS:
        d = milliseconds(d, 0)
    }

    if (unit === DECADE) d = subtract(d, year(d) % 10, 'year')

    if (unit === CENTURY) d = subtract(d, year(d) % 100, 'year')

    if (unit === WEEK) d = weekday(d, 0, firstOfWeek)

    return d
  }

  function endOf(d, unit, firstOfWeek) {
    d = new Date(d)
    d = startOf(d, unit, firstOfWeek)
    d = add(d, 1, unit)
    d = subtract(d, 1, MILI)
    return d
  }

  var eq = createComparer(function(a, b) {
    return a === b
  })
  var gt = createComparer(function(a, b) {
    return a > b
  })
  var gte = createComparer(function(a, b) {
    return a >= b
  })
  var lt = createComparer(function(a, b) {
    return a < b
  })
  var lte = createComparer(function(a, b) {
    return a <= b
  })

  function min() {
    return new Date(Math.min.apply(Math, arguments))
  }

  function max() {
    return new Date(Math.max.apply(Math, arguments))
  }

  function inRange(day, min, max, unit) {
    unit = unit || 'day'

    return (!min || gte(day, min, unit)) && (!max || lte(day, max, unit))
  }

  var milliseconds = createAccessor('Milliseconds')
  var seconds = createAccessor('Seconds')
  var minutes = createAccessor('Minutes')
  var hours = createAccessor('Hours')
  var day = createAccessor('Day')
  var date = createAccessor('Date')
  var month = createAccessor('Month')
  var year = createAccessor('FullYear')

  function weekday(d, val, firstDay) {
    var w = (day(d) + 7 - (firstDay || 0)) % 7

    return val === undefined ? w : add(d, val - w, DAY)
  }

  function monthMath(d, val) {
    var current = month(d),
      newMonth = current + val

    d = month(d, newMonth)

    while (newMonth < 0) newMonth = 12 + newMonth

    //month rollover
    if (month(d) !== newMonth % 12) d = date(d, 0) //move to last of month

    return d
  }

  function createAccessor(method) {
    var hourLength = (function(method) {
      switch (method) {
        case 'Milliseconds':
          return 3600000
        case 'Seconds':
          return 3600
        case 'Minutes':
          return 60
        case 'Hours':
          return 1
        default:
          return null
      }
    })(method)

    return function(d, val) {
      if (val === undefined) return d['get' + method]()

      var dateOut = new Date(d)
      dateOut['set' + method](val)

      if (
        hourLength &&
        dateOut['get' + method]() != val &&
        (method === 'Hours' ||
          (val >= hourLength &&
            dateOut.getHours() - d.getHours() < Math.floor(val / hourLength)))
      ) {
        //Skip DST hour, if it occurs
        dateOut['set' + method](val + hourLength)
      }

      return dateOut
    }
  }

  function createComparer(operator) {
    return function(a, b, unit) {
      return operator(+startOf(a, unit), +startOf(b, unit))
    }
  }

  /* eslint no-fallthrough: off */
  var MILLI = {
    seconds: 1000,
    minutes: 1000 * 60,
    hours: 1000 * 60 * 60,
    day: 1000 * 60 * 60 * 24,
  }
  function firstVisibleDay(date, localizer) {
    var firstOfMonth = startOf(date, 'month')
    return startOf(firstOfMonth, 'week', localizer.startOfWeek())
  }
  function lastVisibleDay(date, localizer) {
    var endOfMonth = endOf(date, 'month')
    return endOf(endOfMonth, 'week', localizer.startOfWeek())
  }
  function visibleDays(date, localizer) {
    var current = firstVisibleDay(date, localizer),
      last = lastVisibleDay(date, localizer),
      days = []

    while (lte(current, last, 'day')) {
      days.push(current)
      current = add(current, 1, 'day')
    }

    return days
  }
  function ceil(date, unit) {
    var floor = startOf(date, unit)
    return eq(floor, date) ? floor : add(floor, 1, unit)
  }
  function range(start, end, unit) {
    if (unit === void 0) {
      unit = 'day'
    }

    var current = start,
      days = []

    while (lte(current, end, unit)) {
      days.push(current)
      current = add(current, 1, unit)
    }

    return days
  }
  function merge(date, time) {
    if (time == null && date == null) return null
    if (time == null) time = new Date()
    if (date == null) date = new Date()
    date = startOf(date, 'day')
    date = hours(date, hours(time))
    date = minutes(date, minutes(time))
    date = seconds(date, seconds(time))
    return milliseconds(date, milliseconds(time))
  }
  function isJustDate(date) {
    return (
      hours(date) === 0 &&
      minutes(date) === 0 &&
      seconds(date) === 0 &&
      milliseconds(date) === 0
    )
  }
  function diff(dateA, dateB, unit) {
    if (!unit || unit === 'milliseconds') return Math.abs(+dateA - +dateB) // the .round() handles an edge case
    // with DST where the total won't be exact
    // since one day in the range may be shorter/longer by an hour

    return Math.round(
      Math.abs(
        +startOf(dateA, unit) / MILLI[unit] -
          +startOf(dateB, unit) / MILLI[unit]
      )
    )
  }

  /**
   * The base implementation of `_.slice` without an iteratee call guard.
   *
   * @private
   * @param {Array} array The array to slice.
   * @param {number} [start=0] The start position.
   * @param {number} [end=array.length] The end position.
   * @returns {Array} Returns the slice of `array`.
   */
  function baseSlice(array, start, end) {
    var index = -1,
      length = array.length

    if (start < 0) {
      start = -start > length ? 0 : length + start
    }
    end = end > length ? length : end
    if (end < 0) {
      end += length
    }
    length = start > end ? 0 : (end - start) >>> 0
    start >>>= 0

    var result = Array(length)
    while (++index < length) {
      result[index] = array[index + start]
    }
    return result
  }

  /**
   * Performs a
   * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * comparison between two values to determine if they are equivalent.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
   * @example
   *
   * var object = { 'a': 1 };
   * var other = { 'a': 1 };
   *
   * _.eq(object, object);
   * // => true
   *
   * _.eq(object, other);
   * // => false
   *
   * _.eq('a', 'a');
   * // => true
   *
   * _.eq('a', Object('a'));
   * // => false
   *
   * _.eq(NaN, NaN);
   * // => true
   */
  function eq$1(value, other) {
    return value === other || (value !== value && other !== other)
  }

  /** Detect free variable `global` from Node.js. */
  var freeGlobal =
    typeof global == 'object' && global && global.Object === Object && global

  /** Detect free variable `self`. */
  var freeSelf =
    typeof self == 'object' && self && self.Object === Object && self

  /** Used as a reference to the global object. */
  var root = freeGlobal || freeSelf || Function('return this')()

  /** Built-in value references. */
  var Symbol$1 = root.Symbol

  /** Used for built-in method references. */
  var objectProto = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$1 = objectProto.hasOwnProperty

  /**
   * Used to resolve the
   * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
   * of values.
   */
  var nativeObjectToString = objectProto.toString

  /** Built-in value references. */
  var symToStringTag = Symbol$1 ? Symbol$1.toStringTag : undefined

  /**
   * A specialized version of `baseGetTag` which ignores `Symbol.toStringTag` values.
   *
   * @private
   * @param {*} value The value to query.
   * @returns {string} Returns the raw `toStringTag`.
   */
  function getRawTag(value) {
    var isOwn = hasOwnProperty$1.call(value, symToStringTag),
      tag = value[symToStringTag]

    try {
      value[symToStringTag] = undefined
      var unmasked = true
    } catch (e) {}

    var result = nativeObjectToString.call(value)
    if (unmasked) {
      if (isOwn) {
        value[symToStringTag] = tag
      } else {
        delete value[symToStringTag]
      }
    }
    return result
  }

  /** Used for built-in method references. */
  var objectProto$1 = Object.prototype

  /**
   * Used to resolve the
   * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
   * of values.
   */
  var nativeObjectToString$1 = objectProto$1.toString

  /**
   * Converts `value` to a string using `Object.prototype.toString`.
   *
   * @private
   * @param {*} value The value to convert.
   * @returns {string} Returns the converted string.
   */
  function objectToString(value) {
    return nativeObjectToString$1.call(value)
  }

  /** `Object#toString` result references. */
  var nullTag = '[object Null]',
    undefinedTag = '[object Undefined]'

  /** Built-in value references. */
  var symToStringTag$1 = Symbol$1 ? Symbol$1.toStringTag : undefined

  /**
   * The base implementation of `getTag` without fallbacks for buggy environments.
   *
   * @private
   * @param {*} value The value to query.
   * @returns {string} Returns the `toStringTag`.
   */
  function baseGetTag(value) {
    if (value == null) {
      return value === undefined ? undefinedTag : nullTag
    }
    return symToStringTag$1 && symToStringTag$1 in Object(value)
      ? getRawTag(value)
      : objectToString(value)
  }

  /**
   * Checks if `value` is the
   * [language type](http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-types)
   * of `Object`. (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an object, else `false`.
   * @example
   *
   * _.isObject({});
   * // => true
   *
   * _.isObject([1, 2, 3]);
   * // => true
   *
   * _.isObject(_.noop);
   * // => true
   *
   * _.isObject(null);
   * // => false
   */
  function isObject(value) {
    var type = typeof value
    return value != null && (type == 'object' || type == 'function')
  }

  /** `Object#toString` result references. */
  var asyncTag = '[object AsyncFunction]',
    funcTag = '[object Function]',
    genTag = '[object GeneratorFunction]',
    proxyTag = '[object Proxy]'

  /**
   * Checks if `value` is classified as a `Function` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a function, else `false`.
   * @example
   *
   * _.isFunction(_);
   * // => true
   *
   * _.isFunction(/abc/);
   * // => false
   */
  function isFunction(value) {
    if (!isObject(value)) {
      return false
    }
    // The use of `Object#toString` avoids issues with the `typeof` operator
    // in Safari 9 which returns 'object' for typed arrays and other constructors.
    var tag = baseGetTag(value)
    return tag == funcTag || tag == genTag || tag == asyncTag || tag == proxyTag
  }

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER = 9007199254740991

  /**
   * Checks if `value` is a valid array-like length.
   *
   * **Note:** This method is loosely based on
   * [`ToLength`](http://ecma-international.org/ecma-262/7.0/#sec-tolength).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a valid length, else `false`.
   * @example
   *
   * _.isLength(3);
   * // => true
   *
   * _.isLength(Number.MIN_VALUE);
   * // => false
   *
   * _.isLength(Infinity);
   * // => false
   *
   * _.isLength('3');
   * // => false
   */
  function isLength(value) {
    return (
      typeof value == 'number' &&
      value > -1 &&
      value % 1 == 0 &&
      value <= MAX_SAFE_INTEGER
    )
  }

  /**
   * Checks if `value` is array-like. A value is considered array-like if it's
   * not a function and has a `value.length` that's an integer greater than or
   * equal to `0` and less than or equal to `Number.MAX_SAFE_INTEGER`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is array-like, else `false`.
   * @example
   *
   * _.isArrayLike([1, 2, 3]);
   * // => true
   *
   * _.isArrayLike(document.body.children);
   * // => true
   *
   * _.isArrayLike('abc');
   * // => true
   *
   * _.isArrayLike(_.noop);
   * // => false
   */
  function isArrayLike(value) {
    return value != null && isLength(value.length) && !isFunction(value)
  }

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER$1 = 9007199254740991

  /** Used to detect unsigned integer values. */
  var reIsUint = /^(?:0|[1-9]\d*)$/

  /**
   * Checks if `value` is a valid array-like index.
   *
   * @private
   * @param {*} value The value to check.
   * @param {number} [length=MAX_SAFE_INTEGER] The upper bounds of a valid index.
   * @returns {boolean} Returns `true` if `value` is a valid index, else `false`.
   */
  function isIndex(value, length) {
    var type = typeof value
    length = length == null ? MAX_SAFE_INTEGER$1 : length

    return (
      !!length &&
      (type == 'number' || (type != 'symbol' && reIsUint.test(value))) &&
      (value > -1 && value % 1 == 0 && value < length)
    )
  }

  /**
   * Checks if the given arguments are from an iteratee call.
   *
   * @private
   * @param {*} value The potential iteratee value argument.
   * @param {*} index The potential iteratee index or key argument.
   * @param {*} object The potential iteratee object argument.
   * @returns {boolean} Returns `true` if the arguments are from an iteratee call,
   *  else `false`.
   */
  function isIterateeCall(value, index, object) {
    if (!isObject(object)) {
      return false
    }
    var type = typeof index
    if (
      type == 'number'
        ? isArrayLike(object) && isIndex(index, object.length)
        : type == 'string' && index in object
    ) {
      return eq$1(object[index], value)
    }
    return false
  }

  /**
   * Checks if `value` is object-like. A value is object-like if it's not `null`
   * and has a `typeof` result of "object".
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is object-like, else `false`.
   * @example
   *
   * _.isObjectLike({});
   * // => true
   *
   * _.isObjectLike([1, 2, 3]);
   * // => true
   *
   * _.isObjectLike(_.noop);
   * // => false
   *
   * _.isObjectLike(null);
   * // => false
   */
  function isObjectLike(value) {
    return value != null && typeof value == 'object'
  }

  /** `Object#toString` result references. */
  var symbolTag = '[object Symbol]'

  /**
   * Checks if `value` is classified as a `Symbol` primitive or object.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a symbol, else `false`.
   * @example
   *
   * _.isSymbol(Symbol.iterator);
   * // => true
   *
   * _.isSymbol('abc');
   * // => false
   */
  function isSymbol(value) {
    return (
      typeof value == 'symbol' ||
      (isObjectLike(value) && baseGetTag(value) == symbolTag)
    )
  }

  /** Used as references for various `Number` constants. */
  var NAN = 0 / 0

  /** Used to match leading and trailing whitespace. */
  var reTrim = /^\s+|\s+$/g

  /** Used to detect bad signed hexadecimal string values. */
  var reIsBadHex = /^[-+]0x[0-9a-f]+$/i

  /** Used to detect binary string values. */
  var reIsBinary = /^0b[01]+$/i

  /** Used to detect octal string values. */
  var reIsOctal = /^0o[0-7]+$/i

  /** Built-in method references without a dependency on `root`. */
  var freeParseInt = parseInt

  /**
   * Converts `value` to a number.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to process.
   * @returns {number} Returns the number.
   * @example
   *
   * _.toNumber(3.2);
   * // => 3.2
   *
   * _.toNumber(Number.MIN_VALUE);
   * // => 5e-324
   *
   * _.toNumber(Infinity);
   * // => Infinity
   *
   * _.toNumber('3.2');
   * // => 3.2
   */
  function toNumber(value) {
    if (typeof value == 'number') {
      return value
    }
    if (isSymbol(value)) {
      return NAN
    }
    if (isObject(value)) {
      var other = typeof value.valueOf == 'function' ? value.valueOf() : value
      value = isObject(other) ? other + '' : other
    }
    if (typeof value != 'string') {
      return value === 0 ? value : +value
    }
    value = value.replace(reTrim, '')
    var isBinary = reIsBinary.test(value)
    return isBinary || reIsOctal.test(value)
      ? freeParseInt(value.slice(2), isBinary ? 2 : 8)
      : reIsBadHex.test(value)
      ? NAN
      : +value
  }

  /** Used as references for various `Number` constants. */
  var INFINITY = 1 / 0,
    MAX_INTEGER = 1.7976931348623157e308

  /**
   * Converts `value` to a finite number.
   *
   * @static
   * @memberOf _
   * @since 4.12.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {number} Returns the converted number.
   * @example
   *
   * _.toFinite(3.2);
   * // => 3.2
   *
   * _.toFinite(Number.MIN_VALUE);
   * // => 5e-324
   *
   * _.toFinite(Infinity);
   * // => 1.7976931348623157e+308
   *
   * _.toFinite('3.2');
   * // => 3.2
   */
  function toFinite(value) {
    if (!value) {
      return value === 0 ? value : 0
    }
    value = toNumber(value)
    if (value === INFINITY || value === -INFINITY) {
      var sign = value < 0 ? -1 : 1
      return sign * MAX_INTEGER
    }
    return value === value ? value : 0
  }

  /**
   * Converts `value` to an integer.
   *
   * **Note:** This method is loosely based on
   * [`ToInteger`](http://www.ecma-international.org/ecma-262/7.0/#sec-tointeger).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {number} Returns the converted integer.
   * @example
   *
   * _.toInteger(3.2);
   * // => 3
   *
   * _.toInteger(Number.MIN_VALUE);
   * // => 0
   *
   * _.toInteger(Infinity);
   * // => 1.7976931348623157e+308
   *
   * _.toInteger('3.2');
   * // => 3
   */
  function toInteger(value) {
    var result = toFinite(value),
      remainder = result % 1

    return result === result ? (remainder ? result - remainder : result) : 0
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeCeil = Math.ceil,
    nativeMax = Math.max

  /**
   * Creates an array of elements split into groups the length of `size`.
   * If `array` can't be split evenly, the final chunk will be the remaining
   * elements.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to process.
   * @param {number} [size=1] The length of each chunk
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the new array of chunks.
   * @example
   *
   * _.chunk(['a', 'b', 'c', 'd'], 2);
   * // => [['a', 'b'], ['c', 'd']]
   *
   * _.chunk(['a', 'b', 'c', 'd'], 3);
   * // => [['a', 'b', 'c'], ['d']]
   */
  function chunk(array, size, guard) {
    if (guard ? isIterateeCall(array, size, guard) : size === undefined) {
      size = 1
    } else {
      size = nativeMax(toInteger(size), 0)
    }
    var length = array == null ? 0 : array.length
    if (!length || size < 1) {
      return []
    }
    var index = 0,
      resIndex = 0,
      result = Array(nativeCeil(length / size))

    while (index < length) {
      result[resIndex++] = baseSlice(array, index, (index += size))
    }
    return result
  }

  var canUseDOM = !!(
    typeof window !== 'undefined' &&
    window.document &&
    window.document.createElement
  )

  /* https://github.com/component/raf */
  var prev = new Date().getTime()

  function fallback(fn) {
    var curr = new Date().getTime()
    var ms = Math.max(0, 16 - (curr - prev))
    var handle = setTimeout(fn, ms)
    prev = curr
    return handle
  }

  var vendors = ['', 'webkit', 'moz', 'o', 'ms']
  var cancelMethod = 'clearTimeout'
  var rafImpl = fallback // eslint-disable-next-line import/no-mutable-exports

  var getKey = function getKey(vendor, k) {
    return (
      vendor +
      (!vendor ? k : k[0].toUpperCase() + k.substr(1)) +
      'AnimationFrame'
    )
  }

  if (canUseDOM) {
    vendors.some(function(vendor) {
      var rafMethod = getKey(vendor, 'request')

      if (rafMethod in window) {
        cancelMethod = getKey(vendor, 'cancel') // @ts-ignore

        rafImpl = function rafImpl(cb) {
          return window[rafMethod](cb)
        }
      }

      return !!rafImpl
    })
  }

  var cancel = function cancel(id) {
    // @ts-ignore
    if (typeof window[cancelMethod] === 'function') window[cancelMethod](id)
  }
  var request = rafImpl

  var EventCell =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(EventCell, _React$Component)

      function EventCell() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = EventCell.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          style = _this$props.style,
          className = _this$props.className,
          event = _this$props.event,
          selected = _this$props.selected,
          isAllDay = _this$props.isAllDay,
          onSelect = _this$props.onSelect,
          _onDoubleClick = _this$props.onDoubleClick,
          _onKeyPress = _this$props.onKeyPress,
          localizer = _this$props.localizer,
          continuesPrior = _this$props.continuesPrior,
          continuesAfter = _this$props.continuesAfter,
          accessors = _this$props.accessors,
          getters = _this$props.getters,
          children = _this$props.children,
          _this$props$component = _this$props.components,
          Event = _this$props$component.event,
          EventWrapper = _this$props$component.eventWrapper,
          slotStart = _this$props.slotStart,
          slotEnd = _this$props.slotEnd,
          props = _objectWithoutPropertiesLoose(_this$props, [
            'style',
            'className',
            'event',
            'selected',
            'isAllDay',
            'onSelect',
            'onDoubleClick',
            'onKeyPress',
            'localizer',
            'continuesPrior',
            'continuesAfter',
            'accessors',
            'getters',
            'children',
            'components',
            'slotStart',
            'slotEnd',
          ])

        delete props.resizable
        var title = accessors.title(event)
        var tooltip = accessors.tooltip(event)
        var end = accessors.end(event)
        var start = accessors.start(event)
        var allDay = accessors.allDay(event)
        var showAsAllDay =
          isAllDay || allDay || diff(start, ceil(end, 'day'), 'day') > 1
        var userProps = getters.eventProp(event, start, end, selected)
        var content = React__default.createElement(
          'div',
          {
            className: 'rbc-event-content',
            title: tooltip || undefined,
          },
          Event
            ? React__default.createElement(Event, {
                event: event,
                continuesPrior: continuesPrior,
                continuesAfter: continuesAfter,
                title: title,
                isAllDay: allDay,
                localizer: localizer,
                slotStart: slotStart,
                slotEnd: slotEnd,
              })
            : title
        )
        return React__default.createElement(
          EventWrapper,
          _extends({}, this.props, {
            type: 'date',
          }),
          React__default.createElement(
            'div',
            _extends({}, props, {
              tabIndex: 0,
              style: _extends({}, userProps.style, style),
              className: clsx('rbc-event', className, userProps.className, {
                'rbc-selected': selected,
                'rbc-event-allday': showAsAllDay,
                'rbc-event-continues-prior': continuesPrior,
                'rbc-event-continues-after': continuesAfter,
              }),
              onClick: function onClick(e) {
                return onSelect && onSelect(event, e)
              },
              onDoubleClick: function onDoubleClick(e) {
                return _onDoubleClick && _onDoubleClick(event, e)
              },
              onKeyPress: function onKeyPress(e) {
                return _onKeyPress && _onKeyPress(event, e)
              },
            }),
            typeof children === 'function' ? children(content) : content
          )
        )
      }

      return EventCell
    })(React__default.Component)

  EventCell.propTypes = {
    event: propTypes.object.isRequired,
    slotStart: propTypes.instanceOf(Date),
    slotEnd: propTypes.instanceOf(Date),
    resizable: propTypes.bool,
    selected: propTypes.bool,
    isAllDay: propTypes.bool,
    continuesPrior: propTypes.bool,
    continuesAfter: propTypes.bool,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object,
    onSelect: propTypes.func,
    onDoubleClick: propTypes.func,
    onKeyPress: propTypes.func,
  }

  function isSelected(event, selected) {
    if (!event || selected == null) return false
    return [].concat(selected).indexOf(event) !== -1
  }
  function slotWidth(rowBox, slots) {
    var rowWidth = rowBox.right - rowBox.left
    var cellWidth = rowWidth / slots
    return cellWidth
  }
  function getSlotAtX(rowBox, x, rtl, slots) {
    var cellWidth = slotWidth(rowBox, slots)
    return rtl
      ? slots - 1 - Math.floor((x - rowBox.left) / cellWidth)
      : Math.floor((x - rowBox.left) / cellWidth)
  }
  function pointInBox(box, _ref) {
    var x = _ref.x,
      y = _ref.y
    return y >= box.top && y <= box.bottom && x >= box.left && x <= box.right
  }
  function dateCellSelection(start, rowBox, box, slots, rtl) {
    var startIdx = -1
    var endIdx = -1
    var lastSlotIdx = slots - 1
    var cellWidth = slotWidth(rowBox, slots) // cell under the mouse

    var currentSlot = getSlotAtX(rowBox, box.x, rtl, slots) // Identify row as either the initial row
    // or the row under the current mouse point

    var isCurrentRow = rowBox.top < box.y && rowBox.bottom > box.y
    var isStartRow = rowBox.top < start.y && rowBox.bottom > start.y // this row's position relative to the start point

    var isAboveStart = start.y > rowBox.bottom
    var isBelowStart = rowBox.top > start.y
    var isBetween = box.top < rowBox.top && box.bottom > rowBox.bottom // this row is between the current and start rows, so entirely selected

    if (isBetween) {
      startIdx = 0
      endIdx = lastSlotIdx
    }

    if (isCurrentRow) {
      if (isBelowStart) {
        startIdx = 0
        endIdx = currentSlot
      } else if (isAboveStart) {
        startIdx = currentSlot
        endIdx = lastSlotIdx
      }
    }

    if (isStartRow) {
      // select the cell under the initial point
      startIdx = endIdx = rtl
        ? lastSlotIdx - Math.floor((start.x - rowBox.left) / cellWidth)
        : Math.floor((start.x - rowBox.left) / cellWidth)

      if (isCurrentRow) {
        if (currentSlot < startIdx) startIdx = currentSlot
        else endIdx = currentSlot //select current range
      } else if (start.y < box.y) {
        // the current row is below start row
        // select cells to the right of the start cell
        endIdx = lastSlotIdx
      } else {
        // select cells to the left of the start cell
        startIdx = 0
      }
    }

    return {
      startIdx: startIdx,
      endIdx: endIdx,
    }
  }

  var _this = undefined

  var Popup = function Popup(_ref) {
    var events = _ref.events,
      selected = _ref.selected,
      getters = _ref.getters,
      accessors = _ref.accessors,
      components = _ref.components,
      onSelect = _ref.onSelect,
      onDoubleClick = _ref.onDoubleClick,
      onKeyPress = _ref.onKeyPress,
      slotStart = _ref.slotStart,
      slotEnd = _ref.slotEnd,
      localizer = _ref.localizer

    if (!events) {
      return null
    }

    return React__default.createElement(
      'div',
      {
        className: 'rbc-overlay',
      },
      React__default.createElement(
        'div',
        {
          className: 'rbc-overlay-header',
        },
        localizer.format(slotStart, 'dayHeaderFormat')
      ),
      events.map(function(event, idx) {
        return React__default.createElement(EventCell, {
          key: idx,
          type: 'popup',
          event: event,
          getters: getters,
          onSelect: onSelect,
          accessors: accessors,
          components: components,
          onDoubleClick: onDoubleClick,
          onKeyPress: onKeyPress,
          continuesPrior: lt(accessors.end(event), slotStart, 'day'),
          continuesAfter: gte(accessors.start(event), slotEnd, 'day'),
          slotStart: slotStart,
          slotEnd: slotEnd,
          selected: isSelected(event, selected),
          draggable: true,
          onDragStart: function onDragStart() {
            return _this.props.handleDragStart(event)
          },
          onDragEnd: function onDragEnd() {
            return _this.props.show()
          },
        })
      })
    )
  }

  Popup.propTypes = {
    events: propTypes.array,
    selected: propTypes.object,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    onSelect: propTypes.func,
    onDoubleClick: propTypes.func,
    onKeyPress: propTypes.func,
    handleDragStart: propTypes.func,
    show: propTypes.func,
    slotStart: propTypes.instanceOf(Date),
    slotEnd: propTypes.number,
  }

  var _typeof =
    typeof Symbol === 'function' && typeof Symbol.iterator === 'symbol'
      ? function(obj) {
          return typeof obj
        }
      : function(obj) {
          return obj &&
            typeof Symbol === 'function' &&
            obj.constructor === Symbol &&
            obj !== Symbol.prototype
            ? 'symbol'
            : typeof obj
        }

  var isBrowser =
    (typeof window === 'undefined' ? 'undefined' : _typeof(window)) ===
      'object' &&
    (typeof document === 'undefined' ? 'undefined' : _typeof(document)) ===
      'object' &&
    document.nodeType === 9

  var prefix = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })

    var _isInBrowser2 = _interopRequireDefault(isBrowser)

    function _interopRequireDefault(obj) {
      return obj && obj.__esModule ? obj : { default: obj }
    }

    var js = ''
    /**
     * Export javascript style and css style vendor prefixes.
     * Based on "transform" support test.
     */

    var css = ''

    // We should not do anything if required serverside.
    if (_isInBrowser2['default']) {
      // Order matters. We need to check Webkit the last one because
      // other vendors use to add Webkit prefixes to some properties
      var jsCssMap = {
        Moz: '-moz-',
        // IE did it wrong again ...
        ms: '-ms-',
        O: '-o-',
        Webkit: '-webkit-',
      }
      var style = document.createElement('p').style
      var testProp = 'Transform'

      for (var key in jsCssMap) {
        if (key + testProp in style) {
          js = key
          css = jsCssMap[key]
          break
        }
      }
    }

    /**
     * Vendor prefix string for the current browser.
     *
     * @type {{js: String, css: String}}
     * @api public
     */
    exports['default'] = { js: js, css: css }
  })

  unwrapExports(prefix)

  var camelize_1 = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    exports['default'] = camelize
    var regExp = /[-\s]+(.)?/g

    /**
     * Convert dash separated strings to camel cased.
     *
     * @param {String} str
     * @return {String}
     */
    function camelize(str) {
      return str.replace(regExp, toUpper)
    }

    function toUpper(match, c) {
      return c ? c.toUpperCase() : ''
    }
  })

  unwrapExports(camelize_1)

  var supportedProperty_1 = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    exports['default'] = supportedProperty

    var _isInBrowser2 = _interopRequireDefault(isBrowser)

    var _prefix2 = _interopRequireDefault(prefix)

    var _camelize2 = _interopRequireDefault(camelize_1)

    function _interopRequireDefault(obj) {
      return obj && obj.__esModule ? obj : { default: obj }
    }

    var el = void 0
    var cache = {}

    if (_isInBrowser2['default']) {
      el = document.createElement('p')

      /**
       * We test every property on vendor prefix requirement.
       * Once tested, result is cached. It gives us up to 70% perf boost.
       * http://jsperf.com/element-style-object-access-vs-plain-object
       *
       * Prefill cache with known css properties to reduce amount of
       * properties we need to feature test at runtime.
       * http://davidwalsh.name/vendor-prefix
       */
      var computed = window.getComputedStyle(document.documentElement, '')
      for (var key in computed) {
        if (!isNaN(key)) cache[computed[key]] = computed[key]
      }
    }

    /**
     * Test if a property is supported, returns supported property with vendor
     * prefix if required. Returns `false` if not supported.
     *
     * @param {String} prop dash separated
     * @return {String|Boolean}
     * @api public
     */
    function supportedProperty(prop) {
      // For server-side rendering.
      if (!el) return prop

      // We have not tested this prop yet, lets do the test.
      if (cache[prop] != null) return cache[prop]

      // Camelization is required because we can't test using
      // css syntax for e.g. in FF.
      // Test if property is supported as it is.
      if ((0, _camelize2['default'])(prop) in el.style) {
        cache[prop] = prop
      }
      // Test if property is supported with vendor prefix.
      else if (
        _prefix2['default'].js + (0, _camelize2['default'])('-' + prop) in
        el.style
      ) {
        cache[prop] = _prefix2['default'].css + prop
      } else {
        cache[prop] = false
      }

      return cache[prop]
    }
  })

  unwrapExports(supportedProperty_1)

  var supportedValue_1 = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    exports['default'] = supportedValue

    var _isInBrowser2 = _interopRequireDefault(isBrowser)

    var _prefix2 = _interopRequireDefault(prefix)

    function _interopRequireDefault(obj) {
      return obj && obj.__esModule ? obj : { default: obj }
    }

    var cache = {}
    var el = void 0

    if (_isInBrowser2['default']) el = document.createElement('p')

    /**
     * Returns prefixed value if needed. Returns `false` if value is not supported.
     *
     * @param {String} property
     * @param {String} value
     * @return {String|Boolean}
     * @api public
     */
    function supportedValue(property, value) {
      // For server-side rendering.
      if (!el) return value

      // It is a string or a number as a string like '1'.
      // We want only prefixable values here.
      if (typeof value !== 'string' || !isNaN(parseInt(value, 10))) return value

      var cacheKey = property + value

      if (cache[cacheKey] != null) return cache[cacheKey]

      // IE can even throw an error in some cases, for e.g. style.content = 'bar'
      try {
        // Test value as it is.
        el.style[property] = value
      } catch (err) {
        cache[cacheKey] = false
        return false
      }

      // Value is supported as it is.
      if (el.style[property] !== '') {
        cache[cacheKey] = value
      } else {
        // Test value with vendor prefix.
        value = _prefix2['default'].css + value

        // Hardcode test to convert "flex" to "-ms-flexbox" for IE10.
        if (value === '-ms-flex') value = '-ms-flexbox'

        el.style[property] = value

        // Value is supported with vendor prefix.
        if (el.style[property] !== '') cache[cacheKey] = value
      }

      if (!cache[cacheKey]) cache[cacheKey] = false

      // Reset style value.
      el.style[property] = ''

      return cache[cacheKey]
    }
  })

  unwrapExports(supportedValue_1)

  var lib = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    exports.supportedValue = exports.supportedProperty = exports.prefix = undefined

    var _prefix2 = _interopRequireDefault(prefix)

    var _supportedProperty2 = _interopRequireDefault(supportedProperty_1)

    var _supportedValue2 = _interopRequireDefault(supportedValue_1)

    function _interopRequireDefault(obj) {
      return obj && obj.__esModule ? obj : { default: obj }
    }

    exports['default'] = {
      prefix: _prefix2['default'],
      supportedProperty: _supportedProperty2['default'],
      supportedValue: _supportedValue2['default'],
    }
    /**
     * CSS Vendor prefix detection and property feature testing.
     *
     * @copyright Oleg Slobodskoi 2015
     * @website https://github.com/jsstyles/css-vendor
     * @license MIT
     */

    exports.prefix = _prefix2['default']
    exports.supportedProperty = _supportedProperty2['default']
    exports.supportedValue = _supportedValue2['default']
  })

  unwrapExports(lib)
  var lib_1 = lib.supportedValue
  var lib_2 = lib.supportedProperty
  var lib_3 = lib.prefix

  /**
   * Helpers.
   */

  var s = 1000
  var m = s * 60
  var h = m * 60
  var d = h * 24
  var y = d * 365.25

  /**
   * Parse or format the given `val`.
   *
   * Options:
   *
   *  - `long` verbose formatting [false]
   *
   * @param {String|Number} val
   * @param {Object} [options]
   * @throws {Error} throw an error if val is not a non-empty string or a number
   * @return {String|Number}
   * @api public
   */

  var ms = function(val, options) {
    options = options || {}
    var type = typeof val
    if (type === 'string' && val.length > 0) {
      return parse(val)
    } else if (type === 'number' && isNaN(val) === false) {
      return options.long ? fmtLong(val) : fmtShort(val)
    }
    throw new Error(
      'val is not a non-empty string or a valid number. val=' +
        JSON.stringify(val)
    )
  }

  /**
   * Parse the given `str` and return milliseconds.
   *
   * @param {String} str
   * @return {Number}
   * @api private
   */

  function parse(str) {
    str = String(str)
    if (str.length > 100) {
      return
    }
    var match = /^((?:\d+)?\.?\d+) *(milliseconds?|msecs?|ms|seconds?|secs?|s|minutes?|mins?|m|hours?|hrs?|h|days?|d|years?|yrs?|y)?$/i.exec(
      str
    )
    if (!match) {
      return
    }
    var n = parseFloat(match[1])
    var type = (match[2] || 'ms').toLowerCase()
    switch (type) {
      case 'years':
      case 'year':
      case 'yrs':
      case 'yr':
      case 'y':
        return n * y
      case 'days':
      case 'day':
      case 'd':
        return n * d
      case 'hours':
      case 'hour':
      case 'hrs':
      case 'hr':
      case 'h':
        return n * h
      case 'minutes':
      case 'minute':
      case 'mins':
      case 'min':
      case 'm':
        return n * m
      case 'seconds':
      case 'second':
      case 'secs':
      case 'sec':
      case 's':
        return n * s
      case 'milliseconds':
      case 'millisecond':
      case 'msecs':
      case 'msec':
      case 'ms':
        return n
      default:
        return undefined
    }
  }

  /**
   * Short format for `ms`.
   *
   * @param {Number} ms
   * @return {String}
   * @api private
   */

  function fmtShort(ms) {
    if (ms >= d) {
      return Math.round(ms / d) + 'd'
    }
    if (ms >= h) {
      return Math.round(ms / h) + 'h'
    }
    if (ms >= m) {
      return Math.round(ms / m) + 'm'
    }
    if (ms >= s) {
      return Math.round(ms / s) + 's'
    }
    return ms + 'ms'
  }

  /**
   * Long format for `ms`.
   *
   * @param {Number} ms
   * @return {String}
   * @api private
   */

  function fmtLong(ms) {
    return (
      plural(ms, d, 'day') ||
      plural(ms, h, 'hour') ||
      plural(ms, m, 'minute') ||
      plural(ms, s, 'second') ||
      ms + ' ms'
    )
  }

  /**
   * Pluralization helper.
   */

  function plural(ms, n, name) {
    if (ms < n) {
      return
    }
    if (ms < n * 1.5) {
      return Math.floor(ms / n) + ' ' + name
    }
    return Math.ceil(ms / n) + ' ' + name + 's'
  }

  var debug = createCommonjsModule(function(module, exports) {
    /**
     * This is the common logic for both the Node.js and web browser
     * implementations of `debug()`.
     *
     * Expose `debug()` as the module.
     */

    exports = module.exports = createDebug.debug = createDebug[
      'default'
    ] = createDebug
    exports.coerce = coerce
    exports.disable = disable
    exports.enable = enable
    exports.enabled = enabled
    exports.humanize = ms

    /**
     * The currently active debug mode names, and names to skip.
     */

    exports.names = []
    exports.skips = []

    /**
     * Map of special "%n" handling functions, for the debug "format" argument.
     *
     * Valid key names are a single, lower or upper-case letter, i.e. "n" and "N".
     */

    exports.formatters = {}

    /**
     * Previous log timestamp.
     */

    var prevTime

    /**
     * Select a color.
     * @param {String} namespace
     * @return {Number}
     * @api private
     */

    function selectColor(namespace) {
      var hash = 0,
        i

      for (i in namespace) {
        hash = (hash << 5) - hash + namespace.charCodeAt(i)
        hash |= 0 // Convert to 32bit integer
      }

      return exports.colors[Math.abs(hash) % exports.colors.length]
    }

    /**
     * Create a debugger with the given `namespace`.
     *
     * @param {String} namespace
     * @return {Function}
     * @api public
     */

    function createDebug(namespace) {
      function debug() {
        // disabled?
        if (!debug.enabled) return

        var self = debug

        // set `diff` timestamp
        var curr = +new Date()
        var ms = curr - (prevTime || curr)
        self.diff = ms
        self.prev = prevTime
        self.curr = curr
        prevTime = curr

        // turn the `arguments` into a proper Array
        var args = new Array(arguments.length)
        for (var i = 0; i < args.length; i++) {
          args[i] = arguments[i]
        }

        args[0] = exports.coerce(args[0])

        if ('string' !== typeof args[0]) {
          // anything else let's inspect with %O
          args.unshift('%O')
        }

        // apply any `formatters` transformations
        var index = 0
        args[0] = args[0].replace(/%([a-zA-Z%])/g, function(match, format) {
          // if we encounter an escaped % then don't increase the array index
          if (match === '%%') return match
          index++
          var formatter = exports.formatters[format]
          if ('function' === typeof formatter) {
            var val = args[index]
            match = formatter.call(self, val)

            // now we need to remove `args[index]` since it's inlined in the `format`
            args.splice(index, 1)
            index--
          }
          return match
        })

        // apply env-specific formatting (colors, etc.)
        exports.formatArgs.call(self, args)

        var logFn = debug.log || exports.log || console.log.bind(console)
        logFn.apply(self, args)
      }

      debug.namespace = namespace
      debug.enabled = exports.enabled(namespace)
      debug.useColors = exports.useColors()
      debug.color = selectColor(namespace)

      // env-specific initialization logic for debug instances
      if ('function' === typeof exports.init) {
        exports.init(debug)
      }

      return debug
    }

    /**
     * Enables a debug mode by namespaces. This can include modes
     * separated by a colon and wildcards.
     *
     * @param {String} namespaces
     * @api public
     */

    function enable(namespaces) {
      exports.save(namespaces)

      exports.names = []
      exports.skips = []

      var split = (typeof namespaces === 'string' ? namespaces : '').split(
        /[\s,]+/
      )
      var len = split.length

      for (var i = 0; i < len; i++) {
        if (!split[i]) continue // ignore empty strings
        namespaces = split[i].replace(/\*/g, '.*?')
        if (namespaces[0] === '-') {
          exports.skips.push(new RegExp('^' + namespaces.substr(1) + '$'))
        } else {
          exports.names.push(new RegExp('^' + namespaces + '$'))
        }
      }
    }

    /**
     * Disable debug output.
     *
     * @api public
     */

    function disable() {
      exports.enable('')
    }

    /**
     * Returns true if the given mode name is enabled, false otherwise.
     *
     * @param {String} name
     * @return {Boolean}
     * @api public
     */

    function enabled(name) {
      var i, len
      for (i = 0, len = exports.skips.length; i < len; i++) {
        if (exports.skips[i].test(name)) {
          return false
        }
      }
      for (i = 0, len = exports.names.length; i < len; i++) {
        if (exports.names[i].test(name)) {
          return true
        }
      }
      return false
    }

    /**
     * Coerce `val`.
     *
     * @param {Mixed} val
     * @return {Mixed}
     * @api private
     */

    function coerce(val) {
      if (val instanceof Error) return val.stack || val.message
      return val
    }
  })
  var debug_1 = debug.coerce
  var debug_2 = debug.disable
  var debug_3 = debug.enable
  var debug_4 = debug.enabled
  var debug_5 = debug.humanize
  var debug_6 = debug.names
  var debug_7 = debug.skips
  var debug_8 = debug.formatters

  var browser = createCommonjsModule(function(module, exports) {
    /**
     * This is the web browser implementation of `debug()`.
     *
     * Expose `debug()` as the module.
     */

    exports = module.exports = debug
    exports.log = log
    exports.formatArgs = formatArgs
    exports.save = save
    exports.load = load
    exports.useColors = useColors
    exports.storage =
      'undefined' != typeof chrome && 'undefined' != typeof chrome.storage
        ? chrome.storage.local
        : localstorage()

    /**
     * Colors.
     */

    exports.colors = [
      'lightseagreen',
      'forestgreen',
      'goldenrod',
      'dodgerblue',
      'darkorchid',
      'crimson',
    ]

    /**
     * Currently only WebKit-based Web Inspectors, Firefox >= v31,
     * and the Firebug extension (any Firefox version) are known
     * to support "%c" CSS customizations.
     *
     * TODO: add a `localStorage` variable to explicitly enable/disable colors
     */

    function useColors() {
      // NB: In an Electron preload script, document will be defined but not fully
      // initialized. Since we know we're in Chrome, we'll just detect this case
      // explicitly
      if (
        typeof window !== 'undefined' &&
        window.process &&
        window.process.type === 'renderer'
      ) {
        return true
      }

      // is webkit? http://stackoverflow.com/a/16459606/376773
      // document is undefined in react-native: https://github.com/facebook/react-native/pull/1632
      return (
        (typeof document !== 'undefined' &&
          document.documentElement &&
          document.documentElement.style &&
          document.documentElement.style.WebkitAppearance) ||
        // is firebug? http://stackoverflow.com/a/398120/376773
        (typeof window !== 'undefined' &&
          window.console &&
          (window.console.firebug ||
            (window.console.exception && window.console.table))) ||
        // is firefox >= v31?
        // https://developer.mozilla.org/en-US/docs/Tools/Web_Console#Styling_messages
        (typeof navigator !== 'undefined' &&
          navigator.userAgent &&
          navigator.userAgent.toLowerCase().match(/firefox\/(\d+)/) &&
          parseInt(RegExp.$1, 10) >= 31) ||
        // double check webkit in userAgent just in case we are in a worker
        (typeof navigator !== 'undefined' &&
          navigator.userAgent &&
          navigator.userAgent.toLowerCase().match(/applewebkit\/(\d+)/))
      )
    }

    /**
     * Map %j to `JSON.stringify()`, since no Web Inspectors do that by default.
     */

    exports.formatters.j = function(v) {
      try {
        return JSON.stringify(v)
      } catch (err) {
        return '[UnexpectedJSONParseError]: ' + err.message
      }
    }

    /**
     * Colorize log arguments if enabled.
     *
     * @api public
     */

    function formatArgs(args) {
      var useColors = this.useColors

      args[0] =
        (useColors ? '%c' : '') +
        this.namespace +
        (useColors ? ' %c' : ' ') +
        args[0] +
        (useColors ? '%c ' : ' ') +
        '+' +
        exports.humanize(this.diff)

      if (!useColors) return

      var c = 'color: ' + this.color
      args.splice(1, 0, c, 'color: inherit')

      // the final "%c" is somewhat tricky, because there could be other
      // arguments passed either before or after the %c, so we need to
      // figure out the correct index to insert the CSS into
      var index = 0
      var lastC = 0
      args[0].replace(/%[a-zA-Z%]/g, function(match) {
        if ('%%' === match) return
        index++
        if ('%c' === match) {
          // we only are interested in the *last* %c
          // (the user may have provided their own)
          lastC = index
        }
      })

      args.splice(lastC, 0, c)
    }

    /**
     * Invokes `console.log()` when available.
     * No-op when `console.log` is not a "function".
     *
     * @api public
     */

    function log() {
      // this hackery is required for IE8/9, where
      // the `console.log` function doesn't have 'apply'
      return (
        'object' === typeof console &&
        console.log &&
        Function.prototype.apply.call(console.log, console, arguments)
      )
    }

    /**
     * Save `namespaces`.
     *
     * @param {String} namespaces
     * @api private
     */

    function save(namespaces) {
      try {
        if (null == namespaces) {
          exports.storage.removeItem('debug')
        } else {
          exports.storage.debug = namespaces
        }
      } catch (e) {}
    }

    /**
     * Load `namespaces`.
     *
     * @return {String} returns the previously persisted debug modes
     * @api private
     */

    function load() {
      var r
      try {
        r = exports.storage.debug
      } catch (e) {}

      // If debug isn't set in LS, and we're in Electron, try to load $DEBUG
      if (!r && typeof process !== 'undefined' && 'env' in process) {
        r = process.env.DEBUG
      }

      return r
    }

    /**
     * Enable namespaces listed in `localStorage.debug` initially.
     */

    exports.enable(load())

    /**
     * Localstorage attempts to return the localstorage.
     *
     * This is necessary because safari throws
     * when a user disables cookies/localstorage
     * and you attempt to access it.
     *
     * @return {LocalStorage}
     * @api private
     */

    function localstorage() {
      try {
        return window.localStorage
      } catch (e) {}
    }
  })
  var browser_1 = browser.log
  var browser_2 = browser.formatArgs
  var browser_3 = browser.save
  var browser_4 = browser.load
  var browser_5 = browser.useColors
  var browser_6 = browser.storage
  var browser_7 = browser.colors

  var node = createCommonjsModule(function(module, exports) {
    /**
     * Module dependencies.
     */

    /**
     * This is the Node.js implementation of `debug()`.
     *
     * Expose `debug()` as the module.
     */

    exports = module.exports = debug
    exports.init = init
    exports.log = log
    exports.formatArgs = formatArgs
    exports.save = save
    exports.load = load
    exports.useColors = useColors

    /**
     * Colors.
     */

    exports.colors = [6, 2, 3, 4, 5, 1]

    /**
     * Build up the default `inspectOpts` object from the environment variables.
     *
     *   $ DEBUG_COLORS=no DEBUG_DEPTH=10 DEBUG_SHOW_HIDDEN=enabled node script.js
     */

    exports.inspectOpts = Object.keys(process.env)
      .filter(function(key) {
        return /^debug_/i.test(key)
      })
      .reduce(function(obj, key) {
        // camel-case
        var prop = key
          .substring(6)
          .toLowerCase()
          .replace(/_([a-z])/g, function(_, k) {
            return k.toUpperCase()
          })

        // coerce string value into JS value
        var val = process.env[key]
        if (/^(yes|on|true|enabled)$/i.test(val)) val = true
        else if (/^(no|off|false|disabled)$/i.test(val)) val = false
        else if (val === 'null') val = null
        else val = Number(val)

        obj[prop] = val
        return obj
      }, {})

    /**
     * The file descriptor to write the `debug()` calls to.
     * Set the `DEBUG_FD` env variable to override with another value. i.e.:
     *
     *   $ DEBUG_FD=3 node script.js 3>debug.log
     */

    var fd = parseInt(process.env.DEBUG_FD, 10) || 2

    if (1 !== fd && 2 !== fd) {
      util.deprecate(function() {},
      'except for stderr(2) and stdout(1), any other usage of DEBUG_FD is deprecated. Override debug.log if you want to use a different log function (https://git.io/debug_fd)')()
    }

    var stream =
      1 === fd
        ? process.stdout
        : 2 === fd
        ? process.stderr
        : createWritableStdioStream(fd)

    /**
     * Is stdout a TTY? Colored output is enabled when `true`.
     */

    function useColors() {
      return 'colors' in exports.inspectOpts
        ? Boolean(exports.inspectOpts.colors)
        : tty.isatty(fd)
    }

    /**
     * Map %o to `util.inspect()`, all on a single line.
     */

    exports.formatters.o = function(v) {
      this.inspectOpts.colors = this.useColors
      return util
        .inspect(v, this.inspectOpts)
        .split('\n')
        .map(function(str) {
          return str.trim()
        })
        .join(' ')
    }

    /**
     * Map %o to `util.inspect()`, allowing multiple lines if needed.
     */

    exports.formatters.O = function(v) {
      this.inspectOpts.colors = this.useColors
      return util.inspect(v, this.inspectOpts)
    }

    /**
     * Adds ANSI color escape codes if enabled.
     *
     * @api public
     */

    function formatArgs(args) {
      var name = this.namespace
      var useColors = this.useColors

      if (useColors) {
        var c = this.color
        var prefix = '  \u001b[3' + c + ';1m' + name + ' ' + '\u001b[0m'

        args[0] = prefix + args[0].split('\n').join('\n' + prefix)
        args.push(
          '\u001b[3' + c + 'm+' + exports.humanize(this.diff) + '\u001b[0m'
        )
      } else {
        args[0] = new Date().toUTCString() + ' ' + name + ' ' + args[0]
      }
    }

    /**
     * Invokes `util.format()` with the specified arguments and writes to `stream`.
     */

    function log() {
      return stream.write(util.format.apply(util, arguments) + '\n')
    }

    /**
     * Save `namespaces`.
     *
     * @param {String} namespaces
     * @api private
     */

    function save(namespaces) {
      if (null == namespaces) {
        // If you set a process.env field to null or undefined, it gets cast to the
        // string 'null' or 'undefined'. Just delete instead.
        delete process.env.DEBUG
      } else {
        process.env.DEBUG = namespaces
      }
    }

    /**
     * Load `namespaces`.
     *
     * @return {String} returns the previously persisted debug modes
     * @api private
     */

    function load() {
      return process.env.DEBUG
    }

    /**
     * Copied from `node/src/node.js`.
     *
     * XXX: It's lame that node doesn't expose this API out-of-the-box. It also
     * relies on the undocumented `tty_wrap.guessHandleType()` which is also lame.
     */

    function createWritableStdioStream(fd) {
      var stream
      var tty_wrap = process.binding('tty_wrap')

      // Note stream._type is used for test-module-load-list.js

      switch (tty_wrap.guessHandleType(fd)) {
        case 'TTY':
          stream = new tty.WriteStream(fd)
          stream._type = 'tty'

          // Hack to have stream not keep the event loop alive.
          // See https://github.com/joyent/node/issues/1726
          if (stream._handle && stream._handle.unref) {
            stream._handle.unref()
          }
          break

        case 'FILE':
          var fs$1 = fs
          stream = new fs$1.SyncWriteStream(fd, { autoClose: false })
          stream._type = 'fs'
          break

        case 'PIPE':
        case 'TCP':
          var net$1 = net
          stream = new net$1.Socket({
            fd: fd,
            readable: false,
            writable: true,
          })

          // FIXME Should probably have an option in net.Socket to create a
          // stream from an existing fd which is writable only. But for now
          // we'll just add this hack and set the `readable` member to false.
          // Test: ./node test/fixtures/echo.js < /etc/passwd
          stream.readable = false
          stream.read = null
          stream._type = 'pipe'

          // FIXME Hack to have stream not keep the event loop alive.
          // See https://github.com/joyent/node/issues/1726
          if (stream._handle && stream._handle.unref) {
            stream._handle.unref()
          }
          break

        default:
          // Probably an error on in uv_guess_handle()
          throw new Error('Implement me. Unknown stream file type!')
      }

      // For supporting legacy API we put the FD here.
      stream.fd = fd

      stream._isStdio = true

      return stream
    }

    /**
     * Init logic for `debug` instances.
     *
     * Create a new `inspectOpts` object in case `useColors` is set
     * differently for a particular `debug` instance.
     */

    function init(debug) {
      debug.inspectOpts = {}

      var keys = Object.keys(exports.inspectOpts)
      for (var i = 0; i < keys.length; i++) {
        debug.inspectOpts[keys[i]] = exports.inspectOpts[keys[i]]
      }
    }

    /**
     * Enable namespaces listed in `process.env.DEBUG` initially.
     */

    exports.enable(load())
  })
  var node_1 = node.init
  var node_2 = node.log
  var node_3 = node.formatArgs
  var node_4 = node.save
  var node_5 = node.load
  var node_6 = node.useColors
  var node_7 = node.colors
  var node_8 = node.inspectOpts

  var src = createCommonjsModule(function(module) {
    /**
     * Detect Electron renderer process, which is node, but we should
     * treat as a browser.
     */

    if (typeof process !== 'undefined' && process.type === 'renderer') {
      module.exports = browser
    } else {
      module.exports = node
    }
  })

  /**
   * lodash 3.9.1 (Custom Build) <https://lodash.com/>
   * Build: `lodash modern modularize exports="npm" -o ./`
   * Copyright 2012-2015 The Dojo Foundation <http://dojofoundation.org/>
   * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
   * Copyright 2009-2015 Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
   * Available under MIT license <https://lodash.com/license>
   */

  /** `Object#toString` result references. */
  var funcTag$1 = '[object Function]'

  /** Used to detect host constructors (Safari > 5). */
  var reIsHostCtor = /^\[object .+?Constructor\]$/

  /**
   * Checks if `value` is object-like.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is object-like, else `false`.
   */
  function isObjectLike$1(value) {
    return !!value && typeof value == 'object'
  }

  /** Used for native method references. */
  var objectProto$2 = Object.prototype

  /** Used to resolve the decompiled source of functions. */
  var fnToString = Function.prototype.toString

  /** Used to check objects for own properties. */
  var hasOwnProperty$2 = objectProto$2.hasOwnProperty

  /**
   * Used to resolve the [`toStringTag`](http://ecma-international.org/ecma-262/6.0/#sec-object.prototype.tostring)
   * of values.
   */
  var objToString = objectProto$2.toString

  /** Used to detect if a method is native. */
  var reIsNative = RegExp(
    '^' +
      fnToString
        .call(hasOwnProperty$2)
        .replace(/[\\^$.*+?()[\]{}|]/g, '\\$&')
        .replace(
          /hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g,
          '$1.*?'
        ) +
      '$'
  )

  /**
   * Gets the native function at `key` of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {string} key The key of the method to get.
   * @returns {*} Returns the function if it's native, else `undefined`.
   */
  function getNative(object, key) {
    var value = object == null ? undefined : object[key]
    return isNative(value) ? value : undefined
  }

  /**
   * Checks if `value` is classified as a `Function` object.
   *
   * @static
   * @memberOf _
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is correctly classified, else `false`.
   * @example
   *
   * _.isFunction(_);
   * // => true
   *
   * _.isFunction(/abc/);
   * // => false
   */
  function isFunction$1(value) {
    // The use of `Object#toString` avoids issues with the `typeof` operator
    // in older versions of Chrome and Safari which return 'function' for regexes
    // and Safari 8 equivalents which return 'object' for typed array constructors.
    return isObject$1(value) && objToString.call(value) == funcTag$1
  }

  /**
   * Checks if `value` is the [language type](https://es5.github.io/#x8) of `Object`.
   * (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
   *
   * @static
   * @memberOf _
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an object, else `false`.
   * @example
   *
   * _.isObject({});
   * // => true
   *
   * _.isObject([1, 2, 3]);
   * // => true
   *
   * _.isObject(1);
   * // => false
   */
  function isObject$1(value) {
    // Avoid a V8 JIT bug in Chrome 19-20.
    // See https://code.google.com/p/v8/issues/detail?id=2291 for more details.
    var type = typeof value
    return !!value && (type == 'object' || type == 'function')
  }

  /**
   * Checks if `value` is a native function.
   *
   * @static
   * @memberOf _
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a native function, else `false`.
   * @example
   *
   * _.isNative(Array.prototype.push);
   * // => true
   *
   * _.isNative(_);
   * // => false
   */
  function isNative(value) {
    if (value == null) {
      return false
    }
    if (isFunction$1(value)) {
      return reIsNative.test(fnToString.call(value))
    }
    return isObjectLike$1(value) && reIsHostCtor.test(value)
  }

  var lodash__getnative = getNative

  /**
   * lodash 3.1.1 (Custom Build) <https://lodash.com/>
   * Build: `lodash modern modularize exports="npm" -o ./`
   * Copyright 2012-2015 The Dojo Foundation <http://dojofoundation.org/>
   * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
   * Copyright 2009-2015 Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
   * Available under MIT license <https://lodash.com/license>
   */

  /** Used as the `TypeError` message for "Functions" methods. */
  var FUNC_ERROR_TEXT = 'Expected a function'

  /* Native method references for those with the same name as other `lodash` methods. */
  var nativeMax$1 = Math.max,
    nativeNow = lodash__getnative(Date, 'now')

  /**
   * Gets the number of milliseconds that have elapsed since the Unix epoch
   * (1 January 1970 00:00:00 UTC).
   *
   * @static
   * @memberOf _
   * @category Date
   * @example
   *
   * _.defer(function(stamp) {
   *   console.log(_.now() - stamp);
   * }, _.now());
   * // => logs the number of milliseconds it took for the deferred function to be invoked
   */
  var now =
    nativeNow ||
    function() {
      return new Date().getTime()
    }

  /**
   * Creates a debounced function that delays invoking `func` until after `wait`
   * milliseconds have elapsed since the last time the debounced function was
   * invoked. The debounced function comes with a `cancel` method to cancel
   * delayed invocations. Provide an options object to indicate that `func`
   * should be invoked on the leading and/or trailing edge of the `wait` timeout.
   * Subsequent calls to the debounced function return the result of the last
   * `func` invocation.
   *
   * **Note:** If `leading` and `trailing` options are `true`, `func` is invoked
   * on the trailing edge of the timeout only if the the debounced function is
   * invoked more than once during the `wait` timeout.
   *
   * See [David Corbacho's article](http://drupalmotion.com/article/debounce-and-throttle-visual-explanation)
   * for details over the differences between `_.debounce` and `_.throttle`.
   *
   * @static
   * @memberOf _
   * @category Function
   * @param {Function} func The function to debounce.
   * @param {number} [wait=0] The number of milliseconds to delay.
   * @param {Object} [options] The options object.
   * @param {boolean} [options.leading=false] Specify invoking on the leading
   *  edge of the timeout.
   * @param {number} [options.maxWait] The maximum time `func` is allowed to be
   *  delayed before it is invoked.
   * @param {boolean} [options.trailing=true] Specify invoking on the trailing
   *  edge of the timeout.
   * @returns {Function} Returns the new debounced function.
   * @example
   *
   * // avoid costly calculations while the window size is in flux
   * jQuery(window).on('resize', _.debounce(calculateLayout, 150));
   *
   * // invoke `sendMail` when the click event is fired, debouncing subsequent calls
   * jQuery('#postbox').on('click', _.debounce(sendMail, 300, {
   *   'leading': true,
   *   'trailing': false
   * }));
   *
   * // ensure `batchLog` is invoked once after 1 second of debounced calls
   * var source = new EventSource('/stream');
   * jQuery(source).on('message', _.debounce(batchLog, 250, {
   *   'maxWait': 1000
   * }));
   *
   * // cancel a debounced call
   * var todoChanges = _.debounce(batchLog, 1000);
   * Object.observe(models.todo, todoChanges);
   *
   * Object.observe(models, function(changes) {
   *   if (_.find(changes, { 'user': 'todo', 'type': 'delete'})) {
   *     todoChanges.cancel();
   *   }
   * }, ['delete']);
   *
   * // ...at some point `models.todo` is changed
   * models.todo.completed = true;
   *
   * // ...before 1 second has passed `models.todo` is deleted
   * // which cancels the debounced `todoChanges` call
   * delete models.todo;
   */
  function debounce(func, wait, options) {
    var args,
      maxTimeoutId,
      result,
      stamp,
      thisArg,
      timeoutId,
      trailingCall,
      lastCalled = 0,
      maxWait = false,
      trailing = true

    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT)
    }
    wait = wait < 0 ? 0 : +wait || 0
    if (options === true) {
      var leading = true
      trailing = false
    } else if (isObject$2(options)) {
      leading = !!options.leading
      maxWait = 'maxWait' in options && nativeMax$1(+options.maxWait || 0, wait)
      trailing = 'trailing' in options ? !!options.trailing : trailing
    }

    function cancel() {
      if (timeoutId) {
        clearTimeout(timeoutId)
      }
      if (maxTimeoutId) {
        clearTimeout(maxTimeoutId)
      }
      lastCalled = 0
      maxTimeoutId = timeoutId = trailingCall = undefined
    }

    function complete(isCalled, id) {
      if (id) {
        clearTimeout(id)
      }
      maxTimeoutId = timeoutId = trailingCall = undefined
      if (isCalled) {
        lastCalled = now()
        result = func.apply(thisArg, args)
        if (!timeoutId && !maxTimeoutId) {
          args = thisArg = undefined
        }
      }
    }

    function delayed() {
      var remaining = wait - (now() - stamp)
      if (remaining <= 0 || remaining > wait) {
        complete(trailingCall, maxTimeoutId)
      } else {
        timeoutId = setTimeout(delayed, remaining)
      }
    }

    function maxDelayed() {
      complete(trailing, timeoutId)
    }

    function debounced() {
      args = arguments
      stamp = now()
      thisArg = this
      trailingCall = trailing && (timeoutId || !leading)

      if (maxWait === false) {
        var leadingCall = leading && !timeoutId
      } else {
        if (!maxTimeoutId && !leading) {
          lastCalled = stamp
        }
        var remaining = maxWait - (stamp - lastCalled),
          isCalled = remaining <= 0 || remaining > maxWait

        if (isCalled) {
          if (maxTimeoutId) {
            maxTimeoutId = clearTimeout(maxTimeoutId)
          }
          lastCalled = stamp
          result = func.apply(thisArg, args)
        } else if (!maxTimeoutId) {
          maxTimeoutId = setTimeout(maxDelayed, remaining)
        }
      }
      if (isCalled && timeoutId) {
        timeoutId = clearTimeout(timeoutId)
      } else if (!timeoutId && wait !== maxWait) {
        timeoutId = setTimeout(delayed, wait)
      }
      if (leadingCall) {
        isCalled = true
        result = func.apply(thisArg, args)
      }
      if (isCalled && !timeoutId && !maxTimeoutId) {
        args = thisArg = undefined
      }
      return result
    }
    debounced.cancel = cancel
    return debounced
  }

  /**
   * Checks if `value` is the [language type](https://es5.github.io/#x8) of `Object`.
   * (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
   *
   * @static
   * @memberOf _
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an object, else `false`.
   * @example
   *
   * _.isObject({});
   * // => true
   *
   * _.isObject([1, 2, 3]);
   * // => true
   *
   * _.isObject(1);
   * // => false
   */
  function isObject$2(value) {
    // Avoid a V8 JIT bug in Chrome 19-20.
    // See https://code.google.com/p/v8/issues/detail?id=2291 for more details.
    var type = typeof value
    return !!value && (type == 'object' || type == 'function')
  }

  var lodash_debounce = debounce

  /**
   * lodash 3.0.4 (Custom Build) <https://lodash.com/>
   * Build: `lodash modern modularize exports="npm" -o ./`
   * Copyright 2012-2015 The Dojo Foundation <http://dojofoundation.org/>
   * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
   * Copyright 2009-2015 Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
   * Available under MIT license <https://lodash.com/license>
   */

  /** Used as the `TypeError` message for "Functions" methods. */
  var FUNC_ERROR_TEXT$1 = 'Expected a function'

  /**
   * Creates a throttled function that only invokes `func` at most once per
   * every `wait` milliseconds. The throttled function comes with a `cancel`
   * method to cancel delayed invocations. Provide an options object to indicate
   * that `func` should be invoked on the leading and/or trailing edge of the
   * `wait` timeout. Subsequent calls to the throttled function return the
   * result of the last `func` call.
   *
   * **Note:** If `leading` and `trailing` options are `true`, `func` is invoked
   * on the trailing edge of the timeout only if the the throttled function is
   * invoked more than once during the `wait` timeout.
   *
   * See [David Corbacho's article](http://drupalmotion.com/article/debounce-and-throttle-visual-explanation)
   * for details over the differences between `_.throttle` and `_.debounce`.
   *
   * @static
   * @memberOf _
   * @category Function
   * @param {Function} func The function to throttle.
   * @param {number} [wait=0] The number of milliseconds to throttle invocations to.
   * @param {Object} [options] The options object.
   * @param {boolean} [options.leading=true] Specify invoking on the leading
   *  edge of the timeout.
   * @param {boolean} [options.trailing=true] Specify invoking on the trailing
   *  edge of the timeout.
   * @returns {Function} Returns the new throttled function.
   * @example
   *
   * // avoid excessively updating the position while scrolling
   * jQuery(window).on('scroll', _.throttle(updatePosition, 100));
   *
   * // invoke `renewToken` when the click event is fired, but not more than once every 5 minutes
   * jQuery('.interactive').on('click', _.throttle(renewToken, 300000, {
   *   'trailing': false
   * }));
   *
   * // cancel a trailing throttled call
   * jQuery(window).on('popstate', throttled.cancel);
   */
  function throttle(func, wait, options) {
    var leading = true,
      trailing = true

    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$1)
    }
    if (options === false) {
      leading = false
    } else if (isObject$3(options)) {
      leading = 'leading' in options ? !!options.leading : leading
      trailing = 'trailing' in options ? !!options.trailing : trailing
    }
    return lodash_debounce(func, wait, {
      leading: leading,
      maxWait: +wait,
      trailing: trailing,
    })
  }

  /**
   * Checks if `value` is the [language type](https://es5.github.io/#x8) of `Object`.
   * (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
   *
   * @static
   * @memberOf _
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an object, else `false`.
   * @example
   *
   * _.isObject({});
   * // => true
   *
   * _.isObject([1, 2, 3]);
   * // => true
   *
   * _.isObject(1);
   * // => false
   */
  function isObject$3(value) {
    // Avoid a V8 JIT bug in Chrome 19-20.
    // See https://code.google.com/p/v8/issues/detail?id=2291 for more details.
    var type = typeof value
    return !!value && (type == 'object' || type == 'function')
  }

  var lodash_throttle = throttle

  var platform = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    var isServer = typeof window === 'undefined'
    var isClient = !isServer
    var WINDOW = isClient ? window : null
    var DOCUMENT = isClient ? document : null

    exports.default = {
      isServer: isServer,
      isClient: isClient,
      window: WINDOW,
      document: DOCUMENT,
    }
    exports.isServer = isServer
    exports.isClient = isClient
    exports.window = WINDOW
    exports.document = DOCUMENT
  })

  unwrapExports(platform)
  var platform_1 = platform.isServer
  var platform_2 = platform.isClient
  var platform_3 = platform.window
  var platform_4 = platform.document

  var utils = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    exports.clientOnly = exports.noop = exports.equalRecords = exports.find = undefined

    var find = function find(f, xs) {
      return xs.reduce(function(b, x) {
        return b ? b : f(x) ? x : null
      }, null)
    }

    var equalRecords = function equalRecords(o1, o2) {
      for (var key in o1) {
        if (o1[key] !== o2[key]) return false
      }
      return true
    }

    var noop = function noop() {
      return undefined
    }

    var clientOnly = function clientOnly(f) {
      return platform.isClient ? f : noop
    }

    exports.default = {
      find: find,
      equalRecords: equalRecords,
      noop: noop,
      clientOnly: clientOnly,
    }
    exports.find = find
    exports.equalRecords = equalRecords
    exports.noop = noop
    exports.clientOnly = clientOnly
  })

  unwrapExports(utils)
  var utils_1 = utils.clientOnly
  var utils_2 = utils.noop
  var utils_3 = utils.equalRecords
  var utils_4 = utils.find

  var layout = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    exports.equalCoords = exports.doesFitWithin = exports.centerOfBoundsFromBounds = exports.centerOfBounds = exports.centerOfSize = exports.axes = exports.pickZone = exports.place = exports.calcRelPos = exports.validTypeValues = exports.types = exports.El = undefined

    function _defineProperty(obj, key, value) {
      if (key in obj) {
        Object.defineProperty(obj, key, {
          value: value,
          enumerable: true,
          configurable: true,
          writable: true,
        })
      } else {
        obj[key] = value
      }
      return obj
    }

    /* Axes System

  This allows us to at-will work in a different orientation
  without having to manually keep track of knowing if we should be using
  x or y positions. */

    var axes = {
      row: {},
      column: {},
    }

    axes.row.main = {
      start: 'x',
      end: 'x2',
      size: 'w',
    }
    axes.row.cross = {
      start: 'y',
      end: 'y2',
      size: 'h',
    }
    axes.column.main = axes.row.cross
    axes.column.cross = axes.row.main

    var types = [
      { name: 'side', values: ['start', 'end'] },
      { name: 'standing', values: ['above', 'right', 'below', 'left'] },
      { name: 'flow', values: ['column', 'row'] },
    ]

    var validTypeValues = types.reduce(function(xs, _ref) {
      var values = _ref.values
      return xs.concat(values)
    }, [])

    var centerOfSize = function centerOfSize(flow, axis, size) {
      return size[axes[flow][axis].size] / 2
    }

    var centerOfBounds = function centerOfBounds(flow, axis, bounds) {
      return bounds[axes[flow][axis].start] + bounds[axes[flow][axis].size] / 2
    }

    var centerOfBoundsFromBounds = function centerOfBoundsFromBounds(
      flow,
      axis,
      boundsTo,
      boundsFrom
    ) {
      return (
        centerOfBounds(flow, axis, boundsTo) -
        boundsFrom[axes[flow][axis].start]
      )
    }

    var place = function place(flow, axis, align, bounds, size) {
      var axisProps = axes[flow][axis]
      return align === 'center'
        ? centerOfBounds(flow, axis, bounds) - centerOfSize(flow, axis, size)
        : align === 'end'
        ? bounds[axisProps.end]
        : align ===
          'start' /* DOM rendering unfolds leftward. Therefore if the slave is positioned before
                                                                                                                                                                    the master then the slave`s position must in addition be pulled back
                                                                                                                                                                    by its [the slave`s] own length. */
        ? bounds[axisProps.start] - size[axisProps.size]
        : null
    }

    /* Element Layout Queries */

    var El = {}

    El.calcBounds = function(el) {
      if (el === platform.window) {
        return {
          x: 0,
          y: 0,
          x2: el.innerWidth,
          y2: el.innerHeight,
          w: el.innerWidth,
          h: el.innerHeight,
        }
      }

      var b = el.getBoundingClientRect()

      return {
        x: b.left,
        y: b.top,
        x2: b.right,
        y2: b.bottom,
        w: b.right - b.left,
        h: b.bottom - b.top,
      }
    }

    El.calcSize = function(el) {
      return el === platform.window
        ? { w: el.innerWidth, h: el.innerHeight }
        : { w: el.offsetWidth, h: el.offsetHeight }
    }

    El.calcScrollSize = function(el) {
      return el === platform.window
        ? {
            w: el.scrollX || el.pageXOffset,
            h: el.scrollY || el.pageYOffset,
          }
        : {
            w: el.scrollLeft,
            h: el.scrollTop,

            /* Misc Utilities */
          }
    }
    var getPreferenceType = function getPreferenceType(preference) {
      return types.reduce(function(found, type) {
        return found
          ? found
          : type.values.indexOf(preference) !== -1
          ? type.name
          : null
      }, null)
    }

    /* Dimension Fit Checks */

    var fitWithinChecker = function fitWithinChecker(dimension) {
      return function(domainSize, itemSize) {
        return domainSize[dimension] >= itemSize[dimension]
      }
    }

    var doesWidthFitWithin = fitWithinChecker('w')
    var doesHeightFitWithin = fitWithinChecker('h')

    var doesFitWithin = function doesFitWithin(domainSize, itemSize) {
      return (
        doesWidthFitWithin(domainSize, itemSize) &&
        doesHeightFitWithin(domainSize, itemSize)
      )
    }

    /* Errors */

    var createPreferenceError = function createPreferenceError(givenValue) {
      return new Error(
        'The given layout placement of "' +
          givenValue +
          '" is not a valid choice. Valid choices are: ' +
          validTypeValues.join(' | ') +
          '.'
      )
    }

    /* Algorithm for picking the best fitting zone for popover. The current technique will loop through all zones picking the last one that fits.
  In the case that none fit we should pick the least-not-fitting zone. */

    var pickZone = function pickZone(opts, frameBounds, targetBounds, size) {
      var t = targetBounds
      var f = frameBounds
      var zones = [
        {
          side: 'start',
          standing: 'above',
          flow: 'column',
          order: -1,
          w: f.x2,
          h: t.y,
        },
        {
          side: 'end',
          standing: 'right',
          flow: 'row',
          order: 1,
          w: f.x2 - t.x2,
          h: f.y2,
        },
        {
          side: 'end',
          standing: 'below',
          flow: 'column',
          order: 1,
          w: f.x2,
          h: f.y2 - t.y2,
        },
        {
          side: 'start',
          standing: 'left',
          flow: 'row',
          order: -1,
          w: t.x,
          h: f.y2,
        },
      ]

      /* Order the zones by the amount of popup that would be cut out if that zone is used.
       The first one in the array is the one that cuts the least amount.
        const area = size.w * size.h  // Popup area is constant and it does not change the order
    */
      zones.forEach(function(z) {
        // TODO Update to satisfy linter
        // eslint-disable-next-line no-param-reassign
        z.cutOff =
          /* area */ -Math.max(0, Math.min(z.w, size.w)) *
          Math.max(0, Math.min(z.h, size.h))
      })
      zones.sort(function(a, b) {
        return a.cutOff - b.cutOff
      })

      var availZones = zones.filter(function(zone) {
        return doesFitWithin(zone, size)
      })

      /* If a place is required pick it from the available zones if possible. */

      if (opts.place) {
        var type = getPreferenceType(opts.place)
        if (!type) throw createPreferenceError(opts.place)
        var finder = function finder(z) {
          return z[type] === opts.place
        }
        return (
          (0, utils.find)(finder, availZones) || (0, utils.find)(finder, zones)
        )
      }

      /* If the preferred side is part of the available zones, use that otherwise
    pick the largest available zone. If there are no available zones, pick the
    largest zone. */

      if (opts.preferPlace) {
        var preferenceType = getPreferenceType(opts.preferPlace)
        if (!preferenceType) throw createPreferenceError(opts.preferPlace)

        // Try to fit first in zone where the pop up fit completely
        var preferredAvailZones = availZones.filter(function(zone) {
          return zone[preferenceType] === opts.preferPlace
        })
        if (preferredAvailZones.length) return preferredAvailZones[0]

        // If there are not areas where the pop up fit completely, it uses the preferred ones
        // in order from the one the fit better
        var preferredZones = zones.filter(function(zone) {
          return zone[preferenceType] === opts.preferPlace
        })
        if (!availZones.length && preferredZones.length)
          return preferredZones[0]
      }

      // Return a zone that fit completely or the one that fit the best
      return availZones.length ? availZones[0] : zones[0]
    }

    /* TODO Document this. */

    var calcRelPos = function calcRelPos(zone, masterBounds, slaveSize) {
      var _ref2

      var _axes$zone$flow = axes[zone.flow],
        main = _axes$zone$flow.main,
        cross = _axes$zone$flow.cross
      /* TODO: The slave is hard-coded to align cross-center with master. */

      var crossAlign = 'center'
      var mainStart = place(
        zone.flow,
        'main',
        zone.side,
        masterBounds,
        slaveSize
      )
      var mainSize = slaveSize[main.size]
      var crossStart = place(
        zone.flow,
        'cross',
        crossAlign,
        masterBounds,
        slaveSize
      )
      var crossSize = slaveSize[cross.size]

      return (
        (_ref2 = {}),
        _defineProperty(_ref2, main.start, mainStart),
        _defineProperty(_ref2, 'mainLength', mainSize),
        _defineProperty(_ref2, main.end, mainStart + mainSize),
        _defineProperty(_ref2, cross.start, crossStart),
        _defineProperty(_ref2, 'crossLength', crossSize),
        _defineProperty(_ref2, cross.end, crossStart + crossSize),
        _ref2
      )
    }

    exports.default = {
      El: El,
      types: types,
      validTypeValues: validTypeValues,
      calcRelPos: calcRelPos,
      place: place,
      pickZone: pickZone,
      axes: axes,
      centerOfSize: centerOfSize,
      centerOfBounds: centerOfBounds,
      centerOfBoundsFromBounds: centerOfBoundsFromBounds,
      doesFitWithin: doesFitWithin,
      equalCoords: utils.equalRecords,
    }
    exports.El = El
    exports.types = types
    exports.validTypeValues = validTypeValues
    exports.calcRelPos = calcRelPos
    exports.place = place
    exports.pickZone = pickZone
    exports.axes = axes
    exports.centerOfSize = centerOfSize
    exports.centerOfBounds = centerOfBounds
    exports.centerOfBoundsFromBounds = centerOfBoundsFromBounds
    exports.doesFitWithin = doesFitWithin
    exports.equalCoords = utils.equalRecords
  })

  unwrapExports(layout)
  var layout_1 = layout.equalCoords
  var layout_2 = layout.doesFitWithin
  var layout_3 = layout.centerOfBoundsFromBounds
  var layout_4 = layout.centerOfBounds
  var layout_5 = layout.centerOfSize
  var layout_6 = layout.axes
  var layout_7 = layout.pickZone
  var layout_8 = layout.place
  var layout_9 = layout.calcRelPos
  var layout_10 = layout.validTypeValues
  var layout_11 = layout.types
  var layout_12 = layout.El

  var onResize = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })
    exports.removeEventListener = exports.addEventListener = exports.off = exports.on = undefined

    /* eslint no-param-reassign: 0 */

    var requestAnimationFrame = platform.isServer
      ? utils.noop
      : platform.window.requestAnimationFrame ||
        platform.window.mozRequestAnimationFrame ||
        platform.window.webkitRequestAnimationFrame ||
        function(fn) {
          platform.window.setTimeout(fn, 20)
        }

    var cancelAnimationFrame = platform.isServer
      ? utils.noop
      : platform.window.cancelAnimationFrame ||
        platform.window.mozCancelAnimationFrame ||
        platform.window.webkitCancelAnimationFrame ||
        platform.window.clearTimeout

    var isIE = platform.isServer ? false : navigator.userAgent.match(/Trident/)

    var namespace = '__resizeDetector__'

    var uninitialize = function uninitialize(el) {
      el[namespace].destroy()
      el[namespace] = undefined
    }

    var createElementHack = function createElementHack() {
      var el = document.createElement('object')
      el.className = 'resize-sensor'
      el.setAttribute(
        'style',
        'display: block; position: absolute; top: 0; left: 0; height: 100%; width: 100%; overflow: hidden; pointer-events: none; z-index: -1;'
      )
      el.setAttribute('class', 'resize-sensor')
      el.setAttribute('tabindex', '-1')
      el.type = 'text/html'
      el.data = 'about:blank'
      return el
    }

    var initialize = function initialize(el) {
      var detector = (el[namespace] = {})
      detector.listeners = []

      var onResize = function onResize(e) {
        /* Keep in mind e.target could be el OR objEl. In this current implementation we don't seem to need to know this but its important
      to not forget e.g. in some future refactoring scenario. */
        if (detector.resizeRAF) cancelAnimationFrame(detector.resizeRAF)
        detector.resizeRAF = requestAnimationFrame(function() {
          detector.listeners.forEach(function(fn) {
            fn(e)
          })
        })
      }

      if (isIE) {
        /* We do not support ie8 and below (or ie9 in compat mode).
      Therefore there is no presence of `attachEvent` here. */
        el.addEventListener('onresize', onResize)
        detector.destroy = function() {
          el.removeEventListener('onresize', onResize)
        }
      } else {
        if (getComputedStyle(el).position === 'static') {
          detector.elWasStaticPosition = true
          el.style.position = 'relative'
        }
        var objEl = createElementHack()
        objEl.onload = function() /* event */ {
          this.contentDocument.defaultView.addEventListener('resize', onResize)
        }
        detector.destroy = function() {
          if (detector.elWasStaticPosition) el.style.position = ''
          if (el.contains(objEl)) {
            // Event handlers will be automatically removed.
            // http://stackoverflow.com/questions/12528049/if-a-dom-element-is-removed-are-its-listeners-also-removed-from-memory
            el.removeChild(objEl)
          }
        }

        el.appendChild(objEl)
      }
    }

    var on = function on(el, fn) {
      /* Window object natively publishes resize events. We handle it as a
    special case here so that users do not have to think about two APIs. */

      if (el === platform.window) {
        platform.window.addEventListener('resize', fn)
        return
      }

      /* Not caching namespace read here beacuse not guaranteed that its available. */

      if (!el[namespace]) initialize(el)
      el[namespace].listeners.push(fn)
    }

    var off = function off(el, fn) {
      if (el === platform.window) {
        platform.window.removeEventListener('resize', fn)
        return
      }
      var detector = el[namespace]
      if (!detector) return
      var i = detector.listeners.indexOf(fn)
      if (i !== -1) detector.listeners.splice(i, 1)
      if (!detector.listeners.length) uninitialize(el)
    }

    exports.default = {
      on: on,
      off: off,
      addEventListener: on,
      removeEventListener: off,
    }
    exports.on = on
    exports.off = off
    exports.addEventListener = on
    exports.removeEventListener = off
  })

  unwrapExports(onResize)
  var onResize_1 = onResize.removeEventListener
  var onResize_2 = onResize.addEventListener
  var onResize_3 = onResize.off
  var onResize_4 = onResize.on

  var tip = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })

    var _react2 = _interopRequireDefault(React__default)

    function _interopRequireDefault(obj) {
      return obj && obj.__esModule ? obj : { default: obj }
    }

    var Tip = function Tip(props) {
      var direction = props.direction

      var size = props.size || 24
      var isPortrait = direction === 'up' || direction === 'down'
      var mainLength = size
      var crossLength = size * 2
      var points =
        direction === 'up'
          ? '0,' +
            mainLength +
            ' ' +
            mainLength +
            ',0, ' +
            crossLength +
            ',' +
            mainLength
          : direction === 'down'
          ? '0,0 ' + mainLength + ',' + mainLength + ', ' + crossLength + ',0'
          : direction === 'left'
          ? mainLength +
            ',0 0,' +
            mainLength +
            ', ' +
            mainLength +
            ',' +
            crossLength
          : '0,0 ' + mainLength + ',' + mainLength + ', 0,' + crossLength
      var svgProps = {
        className: 'Popover-tip',
        width: isPortrait ? crossLength : mainLength,
        height: isPortrait ? mainLength : crossLength,
      }

      return _react2.default.createElement(
        'svg',
        svgProps,
        _react2.default.createElement('polygon', {
          className: 'Popover-tipShape',
          points: points,
        })
      )
    }

    exports.default = Tip
  })

  unwrapExports(tip)

  var build = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', {
      value: true,
    })

    var _extends =
      Object.assign ||
      function(target) {
        for (var i = 1; i < arguments.length; i++) {
          var source = arguments[i]
          for (var key in source) {
            if (Object.prototype.hasOwnProperty.call(source, key)) {
              target[key] = source[key]
            }
          }
        }
        return target
      }

    var _createClass = (function() {
      function defineProperties(target, props) {
        for (var i = 0; i < props.length; i++) {
          var descriptor = props[i]
          descriptor.enumerable = descriptor.enumerable || false
          descriptor.configurable = true
          if ('value' in descriptor) descriptor.writable = true
          Object.defineProperty(target, descriptor.key, descriptor)
        }
      }
      return function(Constructor, protoProps, staticProps) {
        if (protoProps) defineProperties(Constructor.prototype, protoProps)
        if (staticProps) defineProperties(Constructor, staticProps)
        return Constructor
      }
    })()

    var cssVendor = _interopRequireWildcard(lib)

    var _debug2 = _interopRequireDefault(src)

    var _lodash2 = _interopRequireDefault(lodash_throttle)

    var _propTypes2 = _interopRequireDefault(propTypes)

    var _react2 = _interopRequireDefault(React__default)

    var _reactDom2 = _interopRequireDefault(reactDom__default)

    var _layout2 = _interopRequireDefault(layout)

    var _onResize2 = _interopRequireDefault(onResize)

    var _platform2 = _interopRequireDefault(platform)

    var _tip2 = _interopRequireDefault(tip)

    var _utils2 = _interopRequireDefault(utils)

    function _interopRequireDefault(obj) {
      return obj && obj.__esModule ? obj : { default: obj }
    }

    function _interopRequireWildcard(obj) {
      if (obj && obj.__esModule) {
        return obj
      } else {
        var newObj = {}
        if (obj != null) {
          for (var key in obj) {
            if (Object.prototype.hasOwnProperty.call(obj, key))
              newObj[key] = obj[key]
          }
        }
        newObj.default = obj
        return newObj
      }
    }

    function _classCallCheck(instance, Constructor) {
      if (!(instance instanceof Constructor)) {
        throw new TypeError('Cannot call a class as a function')
      }
    }

    function _possibleConstructorReturn(self, call) {
      if (!self) {
        throw new ReferenceError(
          "this hasn't been initialised - super() hasn't been called"
        )
      }
      return call && (typeof call === 'object' || typeof call === 'function')
        ? call
        : self
    }

    function _inherits(subClass, superClass) {
      if (typeof superClass !== 'function' && superClass !== null) {
        throw new TypeError(
          'Super expression must either be null or a function, not ' +
            typeof superClass
        )
      }
      subClass.prototype = Object.create(superClass && superClass.prototype, {
        constructor: {
          value: subClass,
          enumerable: false,
          writable: true,
          configurable: true,
        },
      })
      if (superClass)
        Object.setPrototypeOf
          ? Object.setPrototypeOf(subClass, superClass)
          : (subClass.__proto__ = superClass)
    }

    var log = (0, _debug2.default)('react-popover')

    var supportedCSSValue = _utils2.default.clientOnly(cssVendor.supportedValue)

    var jsprefix = function jsprefix(x) {
      return '' + cssVendor.prefix.js + x
    }

    var cssprefix = function cssprefix(x) {
      return '' + cssVendor.prefix.css + x
    }

    var cssvalue = function cssvalue(prop, value) {
      return supportedCSSValue(prop, value) || cssprefix(value)
    }

    var coreStyle = {
      position: 'absolute',
      top: 0,
      left: 0,
      display: cssvalue('display', 'flex'),
    }

    var faces = {
      above: 'down',
      right: 'left',
      below: 'up',
      left: 'right',

      /* Flow mappings. Each map maps the flow domain to another domain. */
    }
    var flowToTipTranslations = {
      row: 'translateY',
      column: 'translateX',
    }

    var flowToPopoverTranslations = {
      row: 'translateX',
      column: 'translateY',
    }

    var Popover = (function(_React$Component) {
      _inherits(Popover, _React$Component)

      function Popover(props) {
        _classCallCheck(this, Popover)

        var _this = _possibleConstructorReturn(
          this,
          (Popover.__proto__ || Object.getPrototypeOf(Popover)).call(
            this,
            props
          )
        )

        _this.checkTargetReposition = function() {
          if (_this.measureTargetBounds()) _this.resolvePopoverLayout()
        }

        _this.checkForOuterAction = function(event) {
          var isOuterAction =
            !_this.containerEl.contains(event.target) &&
            !_this.targetEl.contains(event.target)
          if (isOuterAction) _this.props.onOuterAction(event)
        }

        _this.onTargetResize = function() {
          log('Recalculating layout because _target_ resized!')
          _this.measureTargetBounds()
          _this.resolvePopoverLayout()
        }

        _this.onPopoverResize = function() {
          log('Recalculating layout because _popover_ resized!')
          _this.measurePopoverSize()
          _this.resolvePopoverLayout()
        }

        _this.onFrameScroll = function() {
          log('Recalculating layout because _frame_ scrolled!')
          _this.measureTargetBounds()
          _this.resolvePopoverLayout()
        }

        _this.onFrameResize = function() {
          log('Recalculating layout because _frame_ resized!')
          _this.measureFrameBounds()
          _this.resolvePopoverLayout()
        }

        _this.getContainerNodeRef = function(containerEl) {
          Object.assign(_this, { containerEl: containerEl })
        }

        _this.state = {
          standing: 'above',
          exited: !_this.props.isOpen, // for animation-dependent rendering, should popover close/open?
          exiting: false, // for tracking in-progress animations
          toggle: _this.props.isOpen || false, // for business logic tracking, should popover close/open?
        }
        return _this
      }

      _createClass(Popover, [
        {
          key: 'componentDidMount',
          value: function componentDidMount() {
            /* Our component needs a DOM Node reference to the child so that it can be
        measured so that we can correctly layout the popover. We do not have any
        control over the child so cannot leverage refs. We could wrap our own
        primitive component around the child but that could lead to breaking the
        uses layout (e.g. the child is a flex item). Leveraging findDOMNode seems
        to be the only functional solution, despite all the general warnings not to
        use it. We have a legitimate use-case. */
            // eslint-disable-next-line
            this.targetEl = _reactDom2.default.findDOMNode(this)
            if (this.props.isOpen) this.enter()
          },
        },
        {
          key: 'componentWillReceiveProps',
          value: function componentWillReceiveProps(propsNext) {
            //log(`Component received props!`, propsNext)
            var willOpen = !this.props.isOpen && propsNext.isOpen
            var willClose = this.props.isOpen && !propsNext.isOpen

            if (willOpen) this.open()
            else if (willClose) this.close()
          },
        },
        {
          key: 'componentDidUpdate',
          value: function componentDidUpdate(propsPrev, statePrev) {
            //log(`Component did update!`)
            var didOpen = !statePrev.toggle && this.state.toggle
            var didClose = statePrev.toggle && !this.state.toggle

            if (didOpen) this.enter()
            else if (didClose) this.exit()
          },
        },
        {
          key: 'componentWillUnmount',
          value: function componentWillUnmount() {
            /* If the Popover is unmounted while animating,
        clear the animation so no setState occured */
            this.animateExitStop()
            /* If the Popover was never opened then then tracking
        initialization never took place and so calling untrack
        would be an error. Also see issue 55. */
            if (this.hasTracked) this.untrackPopover()
          },
        },
        {
          key: 'resolvePopoverLayout',
          value: function resolvePopoverLayout() {
            /* Find the optimal zone to position self. Measure the size of each zone and use the one with
        the greatest area. */

            var pickerSettings = {
              preferPlace: this.props.preferPlace,
              place: this.props.place,

              /* This is a kludge that solves a general problem very specifically for Popover.
          The problem is subtle. When Popover positioning changes such that it resolves at
          a different orientation, its Size will change because the Tip will toggle between
          extending Height or Width. The general problem of course is that calculating
          zone positioning based on current size is non-trivial if the Size can change once
          resolved to a different zone. Infinite recursion can be triggered as we noted here:
          https://github.com/littlebits/react-popover/issues/18. As an example of how this
          could happen in another way: Imagine the user changes the CSS styling of the popover
          based on whether it was `row` or `column` flow. TODO: Find a solution to generally
          solve this problem so that the user is free to change the Popover styles in any
          way at any time for any arbitrary trigger. There may be value in investigating the
          http://overconstrained.io community for its general layout system via the
          constraint-solver Cassowary. */
            }
            if (this.zone)
              this.size[
                this.zone.flow === 'row' ? 'h' : 'w'
              ] += this.props.tipSize
            var zone = _layout2.default.pickZone(
              pickerSettings,
              this.frameBounds,
              this.targetBounds,
              this.size
            )
            if (this.zone)
              this.size[
                this.zone.flow === 'row' ? 'h' : 'w'
              ] -= this.props.tipSize

            var tb = this.targetBounds
            this.zone = zone
            log('zone', zone)

            this.setState({
              standing: zone.standing,
            })

            var axis = _layout2.default.axes[zone.flow]
            log('axes', axis)

            var dockingEdgeBufferLength =
              Math.round(
                getComputedStyle(this.bodyEl).borderRadius.slice(0, -2)
              ) || 0
            var scrollSize = _layout2.default.El.calcScrollSize(this.frameEl)
            scrollSize.main = scrollSize[axis.main.size]
            scrollSize.cross = scrollSize[axis.cross.size]

            /* When positioning self on the cross-axis do not exceed frame bounds. The strategy to achieve
        this is thus: First position cross-axis self to the cross-axis-center of the the target. Then,
        offset self by the amount that self is past the boundaries of frame. */
            var pos = _layout2.default.calcRelPos(zone, tb, this.size)

            /* Offset allows users to control the distance betweent the tip and the target. */
            pos[axis.main.start] += this.props.offset * zone.order

            /* Constrain containerEl Position within frameEl. Try not to penetrate a visually-pleasing buffer from
        frameEl. `frameBuffer` length is based on tipSize and its offset. */

            var frameBuffer = this.props.tipSize + this.props.offset
            var hangingBufferLength =
              dockingEdgeBufferLength * 2 + this.props.tipSize * 2 + frameBuffer
            var frameCrossStart = this.frameBounds[axis.cross.start]
            var frameCrossEnd = this.frameBounds[axis.cross.end]
            var frameCrossLength = this.frameBounds[axis.cross.size]
            var frameCrossInnerLength = frameCrossLength - frameBuffer * 2
            var frameCrossInnerStart = frameCrossStart + frameBuffer
            var frameCrossInnerEnd = frameCrossEnd - frameBuffer
            var popoverCrossStart = pos[axis.cross.start]
            var popoverCrossEnd = pos[axis.cross.end]

            /* If the popover dose not fit into frameCrossLength then just position it to the `frameCrossStart`.
        popoverCrossLength` will now be forced to overflow into the `Frame` */
            if (pos.crossLength > frameCrossLength) {
              log('popoverCrossLength does not fit frame.')
              pos[axis.cross.start] = 0

              /* If the `popoverCrossStart` is forced beyond some threshold of `targetCrossLength` then bound
          it (`popoverCrossStart`). */
            } else if (tb[axis.cross.end] < hangingBufferLength) {
              log(
                'popoverCrossStart cannot hang any further without losing target.'
              )
              pos[axis.cross.start] = tb[axis.cross.end] - hangingBufferLength

              /* checking if the cross start of the target area is within the frame and it makes sense
          to try fitting popover into the frame. */
            } else if (tb[axis.cross.start] > frameCrossInnerEnd) {
              log(
                'popoverCrossStart cannot hang any further without losing target.'
              )
              pos[axis.cross.start] =
                tb[axis.cross.start] - this.size[axis.cross.size]

              /* If the `popoverCrossStart` does not fit within the inner frame (honouring buffers) then
          just center the popover in the remaining `frameCrossLength`. */
            } else if (pos.crossLength > frameCrossInnerLength) {
              log('popoverCrossLength does not fit within buffered frame.')
              pos[axis.cross.start] = (frameCrossLength - pos.crossLength) / 2
            } else if (popoverCrossStart < frameCrossInnerStart) {
              log('popoverCrossStart cannot reverse without exceeding frame.')
              pos[axis.cross.start] = frameCrossInnerStart
            } else if (popoverCrossEnd > frameCrossInnerEnd) {
              log('popoverCrossEnd cannot travel without exceeding frame.')
              pos[axis.cross.start] =
                pos[axis.cross.start] -
                (pos[axis.cross.end] - frameCrossInnerEnd)
            }

            /* So far the link position has been calculated relative to the target. To calculate the absolute
        position we need to factor the `Frame``s scroll position */

            pos[axis.cross.start] += scrollSize.cross
            pos[axis.main.start] += scrollSize.main

            /* Apply `flow` and `order` styles. This can impact subsequent measurements of height and width
        of the container. When tip changes orientation position due to changes from/to `row`/`column`
        width`/`height` will be impacted. Our layout monitoring will catch these cases and automatically
        recalculate layout. */
            if (this.containerEl) {
              this.containerEl.style.flexFlow = zone.flow
              this.containerEl.style[
                jsprefix('FlexFlow')
              ] = this.containerEl.style.flexFlow
            }
            this.bodyEl.style.order = zone.order
            this.bodyEl.style[jsprefix('Order')] = this.bodyEl.style.order

            /* Apply Absolute Positioning. */

            log('pos', pos)
            if (this.containerEl) {
              this.containerEl.style.top = pos.y + 'px'
              this.containerEl.style.left = pos.x + 'px'
            }

            /* Calculate Tip Position */

            var tipCrossPos =
              /* Get the absolute tipCrossCenter. Tip is positioned relative to containerEl
        but it aims at targetCenter which is positioned relative to frameEl... we
        need to cancel the containerEl positioning so as to hit our intended position. */
              _layout2.default.centerOfBoundsFromBounds(
                zone.flow,
                'cross',
                tb,
                pos
              ) +
              /* centerOfBounds does not account for scroll so we need to manually add that
        here. */
              scrollSize.cross -
              /* Center tip relative to self. We do not have to calcualte half-of-tip-size since tip-size
        specifies the length from base to tip which is half of total length already. */
              this.props.tipSize

            if (tipCrossPos < dockingEdgeBufferLength)
              tipCrossPos = dockingEdgeBufferLength
            else if (
              tipCrossPos >
              pos.crossLength - dockingEdgeBufferLength - this.props.tipSize * 2
            ) {
              tipCrossPos =
                pos.crossLength -
                dockingEdgeBufferLength -
                this.props.tipSize * 2
            }

            this.tipEl.style.transform =
              flowToTipTranslations[zone.flow] + '(' + tipCrossPos + 'px)'
            this.tipEl.style[jsprefix('Transform')] = this.tipEl.style.transform
          },
        },
        {
          key: 'measurePopoverSize',
          value: function measurePopoverSize() {
            this.size = _layout2.default.El.calcSize(this.containerEl)
          },
        },
        {
          key: 'measureTargetBounds',
          value: function measureTargetBounds() {
            var newTargetBounds = _layout2.default.El.calcBounds(this.targetEl)

            if (
              this.targetBounds &&
              _layout2.default.equalCoords(this.targetBounds, newTargetBounds)
            ) {
              return false
            }

            this.targetBounds = newTargetBounds
            return true
          },
        },
        {
          key: 'open',
          value: function open() {
            if (this.state.exiting) this.animateExitStop()
            this.setState({ toggle: true, exited: false })
          },
        },
        {
          key: 'close',
          value: function close() {
            this.setState({ toggle: false })
          },
        },
        {
          key: 'enter',
          value: function enter() {
            if (_platform2.default.isServer) return
            log('enter!')
            this.trackPopover()
            this.animateEnter()
          },
        },
        {
          key: 'exit',
          value: function exit() {
            log('exit!')
            this.animateExit()
            this.untrackPopover()
          },
        },
        {
          key: 'animateExitStop',
          value: function animateExitStop() {
            clearTimeout(this.exitingAnimationTimer1)
            clearTimeout(this.exitingAnimationTimer2)
            this.setState({ exiting: false })
          },
        },
        {
          key: 'animateExit',
          value: function animateExit() {
            var _this2 = this

            this.setState({ exiting: true })
            this.exitingAnimationTimer2 = setTimeout(function() {
              setTimeout(function() {
                if (_this2.containerEl) {
                  _this2.containerEl.style.transform =
                    flowToPopoverTranslations[_this2.zone.flow] +
                    '(' +
                    _this2.zone.order * 50 +
                    'px)'
                  _this2.containerEl.style.opacity = '0'
                }
              }, 0)
            }, 0)

            this.exitingAnimationTimer1 = setTimeout(function() {
              _this2.setState({ exited: true, exiting: false })
            }, this.props.enterExitTransitionDurationMs)
          },
        },
        {
          key: 'animateEnter',
          value: function animateEnter() {
            /* Prepare `entering` style so that we can then animate it toward `entered`. */

            this.containerEl.style.transform =
              flowToPopoverTranslations[this.zone.flow] +
              '(' +
              this.zone.order * 50 +
              'px)'
            this.containerEl.style[
              jsprefix('Transform')
            ] = this.containerEl.style.transform
            this.containerEl.style.opacity = '0'

            /* After initial layout apply transition animations. */
            /* Hack: http://stackoverflow.com/questions/3485365/how-can-i-force-webkit-to-redraw-repaint-to-propagate-style-changes */
            this.containerEl.offsetHeight

            /* If enterExitTransitionDurationMs is falsy, tip animation should be also disabled */
            if (this.props.enterExitTransitionDurationMs) {
              this.tipEl.style.transition = 'transform 150ms ease-in'
              this.tipEl.style[jsprefix('Transition')] =
                cssprefix('transform') + ' 150ms ease-in'
            }
            this.containerEl.style.transitionProperty =
              'top, left, opacity, transform'
            this.containerEl.style.transitionDuration =
              this.props.enterExitTransitionDurationMs + 'ms'
            this.containerEl.style.transitionTimingFunction =
              'cubic-bezier(0.230, 1.000, 0.320, 1.000)'
            this.containerEl.style.opacity = '1'
            this.containerEl.style.transform = 'translateY(0)'
            this.containerEl.style[
              jsprefix('Transform')
            ] = this.containerEl.style.transform
          },
        },
        {
          key: 'trackPopover',
          value: function trackPopover() {
            var minScrollRefreshIntervalMs = 200
            var minResizeRefreshIntervalMs = 200

            /* Get references to DOM elements. */

            this.bodyEl = this.containerEl.querySelector('.Popover-body')
            this.tipEl = this.containerEl.querySelector('.Popover-tip')

            /* Note: frame is hardcoded to window now but we think it will
        be a nice feature in the future to allow other frames to be used
        such as local elements that further constrain the popover`s world. */

            this.frameEl = _platform2.default.window
            this.hasTracked = true

            /* Set a general interval for checking if target position changed. There is no way
        to know this information without polling. */
            if (this.props.refreshIntervalMs) {
              this.checkLayoutInterval = setInterval(
                this.checkTargetReposition,
                this.props.refreshIntervalMs
              )
            }

            /* Watch for boundary changes in all deps, and when one of them changes, recalculate layout.
        This layout monitoring must be bound immediately because a layout recalculation can recursively
        cause a change in boundaries. So if we did a one-time force-layout before watching boundaries
        our final position calculations could be wrong. See comments in resolver function for details
        about which parts can trigger recursive recalculation. */

            this.onFrameScroll = (0, _lodash2.default)(
              this.onFrameScroll,
              minScrollRefreshIntervalMs
            )
            this.onFrameResize = (0, _lodash2.default)(
              this.onFrameResize,
              minResizeRefreshIntervalMs
            )
            this.onPopoverResize = (0, _lodash2.default)(
              this.onPopoverResize,
              minResizeRefreshIntervalMs
            )
            this.onTargetResize = (0, _lodash2.default)(
              this.onTargetResize,
              minResizeRefreshIntervalMs
            )

            this.frameEl.addEventListener('scroll', this.onFrameScroll)
            _onResize2.default.on(this.frameEl, this.onFrameResize)
            _onResize2.default.on(this.containerEl, this.onPopoverResize)
            _onResize2.default.on(this.targetEl, this.onTargetResize)

            /* Track user actions on the page. Anything that occurs _outside_ the Popover boundaries
        should close the Popover. */

            _platform2.default.document.addEventListener(
              'mousedown',
              this.checkForOuterAction
            )
            _platform2.default.document.addEventListener(
              'touchstart',
              this.checkForOuterAction
            )

            /* Kickstart layout at first boot. */

            this.measurePopoverSize()
            this.measureFrameBounds()
            this.measureTargetBounds()
            this.resolvePopoverLayout()
          },
        },
        {
          key: 'untrackPopover',
          value: function untrackPopover() {
            clearInterval(this.checkLayoutInterval)
            this.frameEl.removeEventListener('scroll', this.onFrameScroll)
            _onResize2.default.off(this.frameEl, this.onFrameResize)
            _onResize2.default.off(this.containerEl, this.onPopoverResize)
            _onResize2.default.off(this.targetEl, this.onTargetResize)
            _platform2.default.document.removeEventListener(
              'mousedown',
              this.checkForOuterAction
            )
            _platform2.default.document.removeEventListener(
              'touchstart',
              this.checkForOuterAction
            )
            this.hasTracked = false
          },
        },
        {
          key: 'measureFrameBounds',
          value: function measureFrameBounds() {
            this.frameBounds = _layout2.default.El.calcBounds(this.frameEl)
          },
        },
        {
          key: 'render',
          value: function render() {
            var _props = this.props,
              _props$className = _props.className,
              className =
                _props$className === undefined ? '' : _props$className,
              _props$style = _props.style,
              style = _props$style === undefined ? {} : _props$style,
              tipSize = _props.tipSize
            var standing = this.state.standing

            var popoverProps = {
              className: 'Popover Popover-' + standing + ' ' + className,
              style: _extends({}, coreStyle, style),
            }

            var popover = this.state.exited
              ? null
              : _react2.default.createElement(
                  'div',
                  _extends({ ref: this.getContainerNodeRef }, popoverProps),
                  _react2.default.createElement('div', {
                    className: 'Popover-body',
                    children: this.props.body,
                  }),
                  _react2.default.createElement(_tip2.default, {
                    direction: faces[standing],
                    size: tipSize,
                  })
                )
            return [
              this.props.children,
              _platform2.default.isClient &&
                _reactDom2.default.createPortal(
                  popover,
                  this.props.appendTarget
                ),
            ]
          },
        },
      ])

      return Popover
    })(_react2.default.Component)

    Popover.propTypes = {
      body: _propTypes2.default.node.isRequired,
      children: _propTypes2.default.element.isRequired,
      appendTarget: _propTypes2.default.object,
      className: _propTypes2.default.string,
      enterExitTransitionDurationMs: _propTypes2.default.number,
      isOpen: _propTypes2.default.bool,
      offset: _propTypes2.default.number,
      place: _propTypes2.default.oneOf(_layout2.default.validTypeValues),
      preferPlace: _propTypes2.default.oneOf(_layout2.default.validTypeValues),
      refreshIntervalMs: _propTypes2.default.oneOfType([
        _propTypes2.default.number,
        _propTypes2.default.bool,
      ]),
      style: _propTypes2.default.object,
      tipSize: _propTypes2.default.number,
      onOuterAction: _propTypes2.default.func,
    }
    Popover.defaultProps = {
      tipSize: 7,
      preferPlace: null,
      place: null,
      offset: 4,
      isOpen: false,
      onOuterAction: _utils2.default.noop,
      enterExitTransitionDurationMs: 500,
      children: null,
      refreshIntervalMs: 200,
      appendTarget: _platform2.default.isClient
        ? _platform2.default.document.body
        : null,
    }
    exports.default = Popover
  })

  unwrapExports(build)

  // http://stackoverflow.com/questions/33505992/babel-6-changes-how-it-exports-default

  var reactPopover = build.default

  function isDocument(element) {
    return 'nodeType' in element && element.nodeType === document.DOCUMENT_NODE
  }

  function isWindow(node) {
    if ('window' in node && node.window === node) return node
    if (isDocument(node)) return node.defaultView || false
    return false
  }

  /* eslint-disable no-bitwise, no-cond-assign */
  // HTML DOM and SVG DOM may have different support levels,
  // so we need to check on context instead of a document root element.
  function contains(context, node) {
    if (context.contains) return context.contains(node)
    if (context.compareDocumentPosition)
      return context === node || !!(context.compareDocumentPosition(node) & 16)
  }

  function ownerDocument(node) {
    return (node && node.ownerDocument) || document
  }

  function getscrollAccessor(offset) {
    var prop = offset === 'pageXOffset' ? 'scrollLeft' : 'scrollTop'

    function scrollAccessor(node, val) {
      var win = isWindow(node)

      if (val === undefined) {
        return win ? win[offset] : node[prop]
      }

      if (win) {
        win.scrollTo(val, win[offset])
      } else {
        node[prop] = val
      }
    }

    return scrollAccessor
  }

  var scrollLeft = getscrollAccessor('pageXOffset')

  var scrollTop = getscrollAccessor('pageYOffset')

  function offset(node) {
    var doc = ownerDocument(node)
    var box = {
      top: 0,
      left: 0,
      height: 0,
      width: 0,
    }
    var docElem = doc && doc.documentElement // Make sure it's not a disconnected DOM node

    if (!docElem || !contains(docElem, node)) return box
    if (node.getBoundingClientRect !== undefined)
      box = node.getBoundingClientRect()
    box = {
      top: box.top + scrollTop(node) - (docElem.clientTop || 0),
      left: box.left + scrollLeft(node) - (docElem.clientLeft || 0),
      width: box.width,
      height: box.height,
    }
    return box
  }

  function height(node, client) {
    var win = isWindow(node)
    return win
      ? win.innerHeight
      : client
      ? node.clientHeight
      : offset(node).height
  }

  var toArray = Function.prototype.bind.call(Function.prototype.call, [].slice)
  function qsa(element, selector) {
    return toArray(element.querySelectorAll(selector))
  }

  var matchesImpl
  function matches(node, selector) {
    if (!matchesImpl) {
      var body = document.body
      var nativeMatch =
        body.matches ||
        body.matchesSelector ||
        body.webkitMatchesSelector ||
        body.mozMatchesSelector ||
        body.msMatchesSelector

      matchesImpl = function matchesImpl(n, s) {
        return nativeMatch.call(n, s)
      }
    }

    return matchesImpl(node, selector)
  }

  function closest(node, selector, stopAt) {
    if (node.closest && !stopAt) node.closest(selector)
    var nextNode = node

    do {
      if (matches(nextNode, selector)) return nextNode
      nextNode = nextNode.parentElement
    } while (nextNode && nextNode !== stopAt && nextNode.nodeType === document.ELEMENT_NODE)

    return null
  }

  /* eslint-disable no-return-assign */
  var optionsSupported = false
  var onceSupported = false

  try {
    var options = {
      get passive() {
        return (optionsSupported = true)
      },

      get once() {
        // eslint-disable-next-line no-multi-assign
        return (onceSupported = optionsSupported = true)
      },
    }

    if (canUseDOM) {
      window.addEventListener('test', options, options)
      window.removeEventListener('test', options, true)
    }
  } catch (e) {
    /* */
  }

  /**
   * An `addEventListener` ponyfill, supports the `once` option
   */
  function addEventListener(node, eventName, handler, options) {
    if (options && typeof options !== 'boolean' && !onceSupported) {
      var once = options.once,
        capture = options.capture
      var wrappedHandler = handler

      if (!onceSupported && once) {
        wrappedHandler =
          handler.__once ||
          function onceHandler(event) {
            this.removeEventListener(eventName, onceHandler, capture)
            handler.call(this, event)
          }

        handler.__once = wrappedHandler
      }

      node.addEventListener(
        eventName,
        wrappedHandler,
        optionsSupported ? options : capture
      )
    }

    node.addEventListener(eventName, handler, options)
  }

  function removeEventListener(node, eventName, handler, options) {
    var capture =
      options && typeof options !== 'boolean' ? options.capture : options
    node.removeEventListener(eventName, handler, capture)

    if (handler.__once) {
      node.removeEventListener(eventName, handler.__once, capture)
    }
  }

  function listen(node, eventName, handler, options) {
    addEventListener(node, eventName, handler, options)
    return function() {
      removeEventListener(node, eventName, handler, options)
    }
  }

  function addEventListener$1(type, handler, target) {
    if (target === void 0) {
      target = document
    }

    return listen(target, type, handler, {
      passive: false,
    })
  }

  function isOverContainer(container, x, y) {
    return !container || contains(container, document.elementFromPoint(x, y))
  }

  function getEventNodeFromPoint(node, _ref) {
    var clientX = _ref.clientX,
      clientY = _ref.clientY
    var target = document.elementFromPoint(clientX, clientY)
    return closest(target, '.rbc-event', node)
  }
  function isEvent(node, bounds) {
    return !!getEventNodeFromPoint(node, bounds)
  }

  function getEventCoordinates(e) {
    var target = e

    if (e.touches && e.touches.length) {
      target = e.touches[0]
    }

    return {
      clientX: target.clientX,
      clientY: target.clientY,
      pageX: target.pageX,
      pageY: target.pageY,
    }
  }

  var clickTolerance = 5
  var clickInterval = 250

  var Selection =
    /*#__PURE__*/
    (function() {
      function Selection(node, _temp) {
        var _ref2 = _temp === void 0 ? {} : _temp,
          _ref2$global = _ref2.global,
          global = _ref2$global === void 0 ? false : _ref2$global,
          _ref2$longPressThresh = _ref2.longPressThreshold,
          longPressThreshold =
            _ref2$longPressThresh === void 0 ? 250 : _ref2$longPressThresh

        this.isDetached = false
        this.container = node
        this.globalMouse = !node || global
        this.longPressThreshold = longPressThreshold
        this._listeners = Object.create(null)
        this._handleInitialEvent = this._handleInitialEvent.bind(this)
        this._handleMoveEvent = this._handleMoveEvent.bind(this)
        this._handleTerminatingEvent = this._handleTerminatingEvent.bind(this)
        this._keyListener = this._keyListener.bind(this)
        this._dropFromOutsideListener = this._dropFromOutsideListener.bind(this)
        this._dragOverFromOutsideListener = this._dragOverFromOutsideListener.bind(
          this
        ) // Fixes an iOS 10 bug where scrolling could not be prevented on the window.
        // https://github.com/metafizzy/flickity/issues/457#issuecomment-254501356

        this._removeTouchMoveWindowListener = addEventListener$1(
          'touchmove',
          function() {},
          window
        )
        this._removeKeyDownListener = addEventListener$1(
          'keydown',
          this._keyListener
        )
        this._removeKeyUpListener = addEventListener$1(
          'keyup',
          this._keyListener
        )
        this._removeDropFromOutsideListener = addEventListener$1(
          'drop',
          this._dropFromOutsideListener
        )
        this._onDragOverfromOutisde = addEventListener$1(
          'dragover',
          this._dragOverFromOutsideListener
        )

        this._addInitialEventListener()
      }

      var _proto = Selection.prototype

      _proto.on = function on(type, handler) {
        var handlers = this._listeners[type] || (this._listeners[type] = [])
        handlers.push(handler)
        return {
          remove: function remove() {
            var idx = handlers.indexOf(handler)
            if (idx !== -1) handlers.splice(idx, 1)
          },
        }
      }

      _proto.emit = function emit(type) {
        for (
          var _len = arguments.length,
            args = new Array(_len > 1 ? _len - 1 : 0),
            _key = 1;
          _key < _len;
          _key++
        ) {
          args[_key - 1] = arguments[_key]
        }

        var result
        var handlers = this._listeners[type] || []
        handlers.forEach(function(fn) {
          if (result === undefined) result = fn.apply(void 0, args)
        })
        return result
      }

      _proto.teardown = function teardown() {
        this.isDetached = true
        this.listeners = Object.create(null)
        this._removeTouchMoveWindowListener &&
          this._removeTouchMoveWindowListener()
        this._removeInitialEventListener && this._removeInitialEventListener()
        this._removeEndListener && this._removeEndListener()
        this._onEscListener && this._onEscListener()
        this._removeMoveListener && this._removeMoveListener()
        this._removeKeyUpListener && this._removeKeyUpListener()
        this._removeKeyDownListener && this._removeKeyDownListener()
        this._removeDropFromOutsideListener &&
          this._removeDropFromOutsideListener()
      }

      _proto.isSelected = function isSelected(node) {
        var box = this._selectRect
        if (!box || !this.selecting) return false
        return objectsCollide(box, getBoundsForNode(node))
      }

      _proto.filter = function filter(items) {
        var box = this._selectRect //not selecting

        if (!box || !this.selecting) return []
        return items.filter(this.isSelected, this)
      } // Adds a listener that will call the handler only after the user has pressed on the screen
      // without moving their finger for 250ms.

      _proto._addLongPressListener = function _addLongPressListener(
        handler,
        initialEvent
      ) {
        var _this = this

        var timer = null
        var removeTouchMoveListener = null
        var removeTouchEndListener = null

        var handleTouchStart = function handleTouchStart(initialEvent) {
          timer = setTimeout(function() {
            cleanup()
            handler(initialEvent)
          }, _this.longPressThreshold)
          removeTouchMoveListener = addEventListener$1('touchmove', function() {
            return cleanup()
          })
          removeTouchEndListener = addEventListener$1('touchend', function() {
            return cleanup()
          })
        }

        var removeTouchStartListener = addEventListener$1(
          'touchstart',
          handleTouchStart
        )

        var cleanup = function cleanup() {
          if (timer) {
            clearTimeout(timer)
          }

          if (removeTouchMoveListener) {
            removeTouchMoveListener()
          }

          if (removeTouchEndListener) {
            removeTouchEndListener()
          }

          timer = null
          removeTouchMoveListener = null
          removeTouchEndListener = null
        }

        if (initialEvent) {
          handleTouchStart(initialEvent)
        }

        return function() {
          cleanup()
          removeTouchStartListener()
        }
      } // Listen for mousedown and touchstart events. When one is received, disable the other and setup
      // future event handling based on the type of event.

      _proto._addInitialEventListener = function _addInitialEventListener() {
        var _this2 = this

        var removeMouseDownListener = addEventListener$1('mousedown', function(
          e
        ) {
          _this2._removeInitialEventListener()

          _this2._handleInitialEvent(e)

          _this2._removeInitialEventListener = addEventListener$1(
            'mousedown',
            _this2._handleInitialEvent
          )
        })
        var removeTouchStartListener = addEventListener$1(
          'touchstart',
          function(e) {
            _this2._removeInitialEventListener()

            _this2._removeInitialEventListener = _this2._addLongPressListener(
              _this2._handleInitialEvent,
              e
            )
          }
        )

        this._removeInitialEventListener = function() {
          removeMouseDownListener()
          removeTouchStartListener()
        }
      }

      _proto._dropFromOutsideListener = function _dropFromOutsideListener(e) {
        var _getEventCoordinates = getEventCoordinates(e),
          pageX = _getEventCoordinates.pageX,
          pageY = _getEventCoordinates.pageY,
          clientX = _getEventCoordinates.clientX,
          clientY = _getEventCoordinates.clientY

        this.emit('dropFromOutside', {
          x: pageX,
          y: pageY,
          clientX: clientX,
          clientY: clientY,
        })
        e.preventDefault()
      }

      _proto._dragOverFromOutsideListener = function _dragOverFromOutsideListener(
        e
      ) {
        var _getEventCoordinates2 = getEventCoordinates(e),
          pageX = _getEventCoordinates2.pageX,
          pageY = _getEventCoordinates2.pageY,
          clientX = _getEventCoordinates2.clientX,
          clientY = _getEventCoordinates2.clientY

        this.emit('dragOverFromOutside', {
          x: pageX,
          y: pageY,
          clientX: clientX,
          clientY: clientY,
        })
        e.preventDefault()
      }

      _proto._handleInitialEvent = function _handleInitialEvent(e) {
        if (this.isDetached) {
          return
        }

        var _getEventCoordinates3 = getEventCoordinates(e),
          clientX = _getEventCoordinates3.clientX,
          clientY = _getEventCoordinates3.clientY,
          pageX = _getEventCoordinates3.pageX,
          pageY = _getEventCoordinates3.pageY

        var node = this.container(),
          collides,
          offsetData // Right clicks

        if (
          e.which === 3 ||
          e.button === 2 ||
          !isOverContainer(node, clientX, clientY)
        )
          return

        if (!this.globalMouse && node && !contains(node, e.target)) {
          var _normalizeDistance = normalizeDistance(0),
            top = _normalizeDistance.top,
            left = _normalizeDistance.left,
            bottom = _normalizeDistance.bottom,
            right = _normalizeDistance.right

          offsetData = getBoundsForNode(node)
          collides = objectsCollide(
            {
              top: offsetData.top - top,
              left: offsetData.left - left,
              bottom: offsetData.bottom + bottom,
              right: offsetData.right + right,
            },
            {
              top: pageY,
              left: pageX,
            }
          )
          if (!collides) return
        }

        var result = this.emit(
          'beforeSelect',
          (this._initialEventData = {
            isTouch: /^touch/.test(e.type),
            x: pageX,
            y: pageY,
            clientX: clientX,
            clientY: clientY,
          })
        )
        if (result === false) return

        switch (e.type) {
          case 'mousedown':
            this._removeEndListener = addEventListener$1(
              'mouseup',
              this._handleTerminatingEvent
            )
            this._onEscListener = addEventListener$1(
              'keydown',
              this._handleTerminatingEvent
            )
            this._removeMoveListener = addEventListener$1(
              'mousemove',
              this._handleMoveEvent
            )
            break

          case 'touchstart':
            this._handleMoveEvent(e)

            this._removeEndListener = addEventListener$1(
              'touchend',
              this._handleTerminatingEvent
            )
            this._removeMoveListener = addEventListener$1(
              'touchmove',
              this._handleMoveEvent
            )
            break

          default:
            break
        }
      }

      _proto._handleTerminatingEvent = function _handleTerminatingEvent(e) {
        var _getEventCoordinates4 = getEventCoordinates(e),
          pageX = _getEventCoordinates4.pageX,
          pageY = _getEventCoordinates4.pageY

        this.selecting = false
        this._removeEndListener && this._removeEndListener()
        this._removeMoveListener && this._removeMoveListener()
        if (!this._initialEventData) return
        var inRoot = !this.container || contains(this.container(), e.target)
        var bounds = this._selectRect
        var click = this.isClick(pageX, pageY)
        this._initialEventData = null

        if (e.key === 'Escape') {
          return this.emit('reset')
        }

        if (!inRoot) {
          return this.emit('reset')
        }

        if (click && inRoot) {
          return this._handleClickEvent(e)
        } // User drag-clicked in the Selectable area

        if (!click) return this.emit('select', bounds)
      }

      _proto._handleClickEvent = function _handleClickEvent(e) {
        var _getEventCoordinates5 = getEventCoordinates(e),
          pageX = _getEventCoordinates5.pageX,
          pageY = _getEventCoordinates5.pageY,
          clientX = _getEventCoordinates5.clientX,
          clientY = _getEventCoordinates5.clientY

        var now = new Date().getTime()

        if (
          this._lastClickData &&
          now - this._lastClickData.timestamp < clickInterval
        ) {
          // Double click event
          this._lastClickData = null
          return this.emit('doubleClick', {
            x: pageX,
            y: pageY,
            clientX: clientX,
            clientY: clientY,
          })
        } // Click event

        this._lastClickData = {
          timestamp: now,
        }
        return this.emit('click', {
          x: pageX,
          y: pageY,
          clientX: clientX,
          clientY: clientY,
        })
      }

      _proto._handleMoveEvent = function _handleMoveEvent(e) {
        if (this._initialEventData === null || this.isDetached) {
          return
        }

        var _this$_initialEventDa = this._initialEventData,
          x = _this$_initialEventDa.x,
          y = _this$_initialEventDa.y

        var _getEventCoordinates6 = getEventCoordinates(e),
          pageX = _getEventCoordinates6.pageX,
          pageY = _getEventCoordinates6.pageY

        var w = Math.abs(x - pageX)
        var h = Math.abs(y - pageY)
        var left = Math.min(pageX, x),
          top = Math.min(pageY, y),
          old = this.selecting // Prevent emitting selectStart event until mouse is moved.
        // in Chrome on Windows, mouseMove event may be fired just after mouseDown event.

        if (this.isClick(pageX, pageY) && !old && !(w || h)) {
          return
        }

        this.selecting = true
        this._selectRect = {
          top: top,
          left: left,
          x: pageX,
          y: pageY,
          right: left + w,
          bottom: top + h,
        }

        if (!old) {
          this.emit('selectStart', this._initialEventData)
        }

        if (!this.isClick(pageX, pageY))
          this.emit('selecting', this._selectRect)
        e.preventDefault()
      }

      _proto._keyListener = function _keyListener(e) {
        this.ctrl = e.metaKey || e.ctrlKey
      }

      _proto.isClick = function isClick(pageX, pageY) {
        var _this$_initialEventDa2 = this._initialEventData,
          x = _this$_initialEventDa2.x,
          y = _this$_initialEventDa2.y,
          isTouch = _this$_initialEventDa2.isTouch
        return (
          !isTouch &&
          Math.abs(pageX - x) <= clickTolerance &&
          Math.abs(pageY - y) <= clickTolerance
        )
      }

      return Selection
    })()
  /**
   * Resolve the disance prop from either an Int or an Object
   * @return {Object}
   */

  function normalizeDistance(distance) {
    if (distance === void 0) {
      distance = 0
    }

    if (typeof distance !== 'object')
      distance = {
        top: distance,
        left: distance,
        right: distance,
        bottom: distance,
      }
    return distance
  }
  /**
   * Given two objects containing "top", "left", "offsetWidth" and "offsetHeight"
   * properties, determine if they collide.
   * @param  {Object|HTMLElement} a
   * @param  {Object|HTMLElement} b
   * @return {bool}
   */

  function objectsCollide(nodeA, nodeB, tolerance) {
    if (tolerance === void 0) {
      tolerance = 0
    }

    var _getBoundsForNode = getBoundsForNode(nodeA),
      aTop = _getBoundsForNode.top,
      aLeft = _getBoundsForNode.left,
      _getBoundsForNode$rig = _getBoundsForNode.right,
      aRight = _getBoundsForNode$rig === void 0 ? aLeft : _getBoundsForNode$rig,
      _getBoundsForNode$bot = _getBoundsForNode.bottom,
      aBottom = _getBoundsForNode$bot === void 0 ? aTop : _getBoundsForNode$bot

    var _getBoundsForNode2 = getBoundsForNode(nodeB),
      bTop = _getBoundsForNode2.top,
      bLeft = _getBoundsForNode2.left,
      _getBoundsForNode2$ri = _getBoundsForNode2.right,
      bRight = _getBoundsForNode2$ri === void 0 ? bLeft : _getBoundsForNode2$ri,
      _getBoundsForNode2$bo = _getBoundsForNode2.bottom,
      bBottom = _getBoundsForNode2$bo === void 0 ? bTop : _getBoundsForNode2$bo

    return !// 'a' bottom doesn't touch 'b' top
    (
      aBottom - tolerance < bTop || // 'a' top doesn't touch 'b' bottom
      aTop + tolerance > bBottom || // 'a' right doesn't touch 'b' left
      aRight - tolerance < bLeft || // 'a' left doesn't touch 'b' right
      aLeft + tolerance > bRight
    )
  }
  /**
   * Given a node, get everything needed to calculate its boundaries
   * @param  {HTMLElement} node
   * @return {Object}
   */

  function getBoundsForNode(node) {
    if (!node.getBoundingClientRect) return node
    var rect = node.getBoundingClientRect(),
      left = rect.left + pageOffset('left'),
      top = rect.top + pageOffset('top')
    return {
      top: top,
      left: left,
      right: (node.offsetWidth || 0) + left,
      bottom: (node.offsetHeight || 0) + top,
    }
  }

  function pageOffset(dir) {
    if (dir === 'left')
      return window.pageXOffset || document.body.scrollLeft || 0
    if (dir === 'top') return window.pageYOffset || document.body.scrollTop || 0
  }

  var BackgroundCells =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(BackgroundCells, _React$Component)

      function BackgroundCells(props, context) {
        var _this

        _this = _React$Component.call(this, props, context) || this
        _this.state = {
          selecting: false,
        }
        return _this
      }

      var _proto = BackgroundCells.prototype

      _proto.componentDidMount = function componentDidMount() {
        this.props.selectable && this._selectable()
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        this._teardownSelectable()
      }

      _proto.UNSAFE_componentWillReceiveProps = function UNSAFE_componentWillReceiveProps(
        nextProps
      ) {
        if (nextProps.selectable && !this.props.selectable) this._selectable()
        if (!nextProps.selectable && this.props.selectable)
          this._teardownSelectable()
      }

      _proto.render = function render() {
        var _this$props = this.props,
          range = _this$props.range,
          getNow = _this$props.getNow,
          getters = _this$props.getters,
          currentDate = _this$props.date,
          Wrapper = _this$props.components.dateCellWrapper
        var _this$state = this.state,
          selecting = _this$state.selecting,
          startIdx = _this$state.startIdx,
          endIdx = _this$state.endIdx
        var current = getNow()
        return React__default.createElement(
          'div',
          {
            className: 'rbc-row-bg',
          },
          range.map(function(date, index) {
            var selected = selecting && index >= startIdx && index <= endIdx

            var _getters$dayProp = getters.dayProp(date),
              className = _getters$dayProp.className,
              style = _getters$dayProp.style

            return React__default.createElement(
              Wrapper,
              {
                key: index,
                value: date,
                range: range,
              },
              React__default.createElement('div', {
                style: style,
                className: clsx(
                  'rbc-day-bg',
                  className,
                  selected && 'rbc-selected-cell',
                  eq(date, current, 'day') && 'rbc-today',
                  currentDate &&
                    month(currentDate) !== month(date) &&
                    'rbc-off-range-bg'
                ),
              })
            )
          })
        )
      }

      _proto._selectable = function _selectable() {
        var _this2 = this

        var node = reactDom.findDOMNode(this)
        var selector = (this._selector = new Selection(this.props.container, {
          longPressThreshold: this.props.longPressThreshold,
        }))

        var selectorClicksHandler = function selectorClicksHandler(
          point,
          actionType
        ) {
          if (!isEvent(reactDom.findDOMNode(_this2), point)) {
            var rowBox = getBoundsForNode(node)
            var _this2$props = _this2.props,
              range = _this2$props.range,
              rtl = _this2$props.rtl

            if (pointInBox(rowBox, point)) {
              var currentCell = getSlotAtX(rowBox, point.x, rtl, range.length)

              _this2._selectSlot({
                startIdx: currentCell,
                endIdx: currentCell,
                action: actionType,
                box: point,
              })
            }
          }

          _this2._initial = {}

          _this2.setState({
            selecting: false,
          })
        }

        selector.on('selecting', function(box) {
          var _this2$props2 = _this2.props,
            range = _this2$props2.range,
            rtl = _this2$props2.rtl
          var startIdx = -1
          var endIdx = -1

          if (!_this2.state.selecting) {
            notify(_this2.props.onSelectStart, [box])
            _this2._initial = {
              x: box.x,
              y: box.y,
            }
          }

          if (selector.isSelected(node)) {
            var nodeBox = getBoundsForNode(node)

            var _dateCellSelection = dateCellSelection(
              _this2._initial,
              nodeBox,
              box,
              range.length,
              rtl
            )

            startIdx = _dateCellSelection.startIdx
            endIdx = _dateCellSelection.endIdx
          }

          _this2.setState({
            selecting: true,
            startIdx: startIdx,
            endIdx: endIdx,
          })
        })
        selector.on('beforeSelect', function(box) {
          if (_this2.props.selectable !== 'ignoreEvents') return
          return !isEvent(reactDom.findDOMNode(_this2), box)
        })
        selector.on('click', function(point) {
          return selectorClicksHandler(point, 'click')
        })
        selector.on('doubleClick', function(point) {
          return selectorClicksHandler(point, 'doubleClick')
        })
        selector.on('select', function(bounds) {
          _this2._selectSlot(
            _extends({}, _this2.state, {
              action: 'select',
              bounds: bounds,
            })
          )

          _this2._initial = {}

          _this2.setState({
            selecting: false,
          })

          notify(_this2.props.onSelectEnd, [_this2.state])
        })
      }

      _proto._teardownSelectable = function _teardownSelectable() {
        if (!this._selector) return

        this._selector.teardown()

        this._selector = null
      }

      _proto._selectSlot = function _selectSlot(_ref) {
        var endIdx = _ref.endIdx,
          startIdx = _ref.startIdx,
          action = _ref.action,
          bounds = _ref.bounds,
          box = _ref.box
        if (endIdx !== -1 && startIdx !== -1)
          this.props.onSelectSlot &&
            this.props.onSelectSlot({
              start: startIdx,
              end: endIdx,
              action: action,
              bounds: bounds,
              box: box,
              resourceId: this.props.resourceId,
            })
      }

      return BackgroundCells
    })(React__default.Component)

  BackgroundCells.propTypes = {
    date: propTypes.instanceOf(Date),
    getNow: propTypes.func.isRequired,
    getters: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    container: propTypes.func,
    dayPropGetter: propTypes.func,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onSelectSlot: propTypes.func.isRequired,
    onSelectEnd: propTypes.func,
    onSelectStart: propTypes.func,
    range: propTypes.arrayOf(propTypes.instanceOf(Date)),
    rtl: propTypes.bool,
    type: propTypes.string,
    resourceId: propTypes.any,
  }

  /* eslint-disable react/prop-types */

  var EventRowMixin = {
    propTypes: {
      slotMetrics: propTypes.object.isRequired,
      selected: propTypes.object,
      isAllDay: propTypes.bool,
      accessors: propTypes.object.isRequired,
      localizer: propTypes.object.isRequired,
      components: propTypes.object.isRequired,
      getters: propTypes.object.isRequired,
      onSelect: propTypes.func,
      onDoubleClick: propTypes.func,
      onKeyPress: propTypes.func,
    },
    defaultProps: {
      segments: [],
      selected: {},
    },
    renderEvent: function renderEvent(props, event) {
      var selected = props.selected,
        _ = props.isAllDay,
        accessors = props.accessors,
        getters = props.getters,
        onSelect = props.onSelect,
        onDoubleClick = props.onDoubleClick,
        onKeyPress = props.onKeyPress,
        localizer = props.localizer,
        slotMetrics = props.slotMetrics,
        components = props.components,
        resizable = props.resizable
      var continuesPrior = slotMetrics.continuesPrior(event)
      var continuesAfter = slotMetrics.continuesAfter(event)
      return React__default.createElement(EventCell, {
        event: event,
        getters: getters,
        localizer: localizer,
        accessors: accessors,
        components: components,
        onSelect: onSelect,
        onDoubleClick: onDoubleClick,
        onKeyPress: onKeyPress,
        continuesPrior: continuesPrior,
        continuesAfter: continuesAfter,
        slotStart: slotMetrics.first,
        slotEnd: slotMetrics.last,
        selected: isSelected(event, selected),
        resizable: resizable,
      })
    },
    renderSpan: function renderSpan(slots, len, key, content) {
      if (content === void 0) {
        content = ' '
      }

      var per = (Math.abs(len) / slots) * 100 + '%'
      return React__default.createElement(
        'div',
        {
          key: key,
          className: 'rbc-row-segment', // IE10/11 need max-width. flex-basis doesn't respect box-sizing
          style: {
            WebkitFlexBasis: per,
            flexBasis: per,
            maxWidth: per,
          },
        },
        content
      )
    },
  }

  var EventRow =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(EventRow, _React$Component)

      function EventRow() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = EventRow.prototype

      _proto.render = function render() {
        var _this = this

        var _this$props = this.props,
          segments = _this$props.segments,
          slots = _this$props.slotMetrics.slots,
          className = _this$props.className
        var lastEnd = 1
        return React__default.createElement(
          'div',
          {
            className: clsx(className, 'rbc-row'),
          },
          segments.reduce(function(row, _ref, li) {
            var event = _ref.event,
              left = _ref.left,
              right = _ref.right,
              span = _ref.span
            var key = '_lvl_' + li
            var gap = left - lastEnd
            var content = EventRowMixin.renderEvent(_this.props, event)
            if (gap)
              row.push(EventRowMixin.renderSpan(slots, gap, key + '_gap'))
            row.push(EventRowMixin.renderSpan(slots, span, key, content))
            lastEnd = right + 1
            return row
          }, [])
        )
      }

      return EventRow
    })(React__default.Component)

  EventRow.propTypes = _extends(
    {
      segments: propTypes.array,
    },
    EventRowMixin.propTypes
  )
  EventRow.defaultProps = _extends({}, EventRowMixin.defaultProps)

  /**
   * The base implementation of `_.findIndex` and `_.findLastIndex` without
   * support for iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {Function} predicate The function invoked per iteration.
   * @param {number} fromIndex The index to search from.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function baseFindIndex(array, predicate, fromIndex, fromRight) {
    var length = array.length,
      index = fromIndex + (fromRight ? 1 : -1)

    while (fromRight ? index-- : ++index < length) {
      if (predicate(array[index], index, array)) {
        return index
      }
    }
    return -1
  }

  /**
   * Removes all key-value entries from the list cache.
   *
   * @private
   * @name clear
   * @memberOf ListCache
   */
  function listCacheClear() {
    this.__data__ = []
    this.size = 0
  }

  /**
   * Gets the index at which the `key` is found in `array` of key-value pairs.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} key The key to search for.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function assocIndexOf(array, key) {
    var length = array.length
    while (length--) {
      if (eq$1(array[length][0], key)) {
        return length
      }
    }
    return -1
  }

  /** Used for built-in method references. */
  var arrayProto = Array.prototype

  /** Built-in value references. */
  var splice = arrayProto.splice

  /**
   * Removes `key` and its value from the list cache.
   *
   * @private
   * @name delete
   * @memberOf ListCache
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function listCacheDelete(key) {
    var data = this.__data__,
      index = assocIndexOf(data, key)

    if (index < 0) {
      return false
    }
    var lastIndex = data.length - 1
    if (index == lastIndex) {
      data.pop()
    } else {
      splice.call(data, index, 1)
    }
    --this.size
    return true
  }

  /**
   * Gets the list cache value for `key`.
   *
   * @private
   * @name get
   * @memberOf ListCache
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function listCacheGet(key) {
    var data = this.__data__,
      index = assocIndexOf(data, key)

    return index < 0 ? undefined : data[index][1]
  }

  /**
   * Checks if a list cache value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf ListCache
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function listCacheHas(key) {
    return assocIndexOf(this.__data__, key) > -1
  }

  /**
   * Sets the list cache `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf ListCache
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the list cache instance.
   */
  function listCacheSet(key, value) {
    var data = this.__data__,
      index = assocIndexOf(data, key)

    if (index < 0) {
      ++this.size
      data.push([key, value])
    } else {
      data[index][1] = value
    }
    return this
  }

  /**
   * Creates an list cache object.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function ListCache(entries) {
    var index = -1,
      length = entries == null ? 0 : entries.length

    this.clear()
    while (++index < length) {
      var entry = entries[index]
      this.set(entry[0], entry[1])
    }
  }

  // Add methods to `ListCache`.
  ListCache.prototype.clear = listCacheClear
  ListCache.prototype['delete'] = listCacheDelete
  ListCache.prototype.get = listCacheGet
  ListCache.prototype.has = listCacheHas
  ListCache.prototype.set = listCacheSet

  /**
   * Removes all key-value entries from the stack.
   *
   * @private
   * @name clear
   * @memberOf Stack
   */
  function stackClear() {
    this.__data__ = new ListCache()
    this.size = 0
  }

  /**
   * Removes `key` and its value from the stack.
   *
   * @private
   * @name delete
   * @memberOf Stack
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function stackDelete(key) {
    var data = this.__data__,
      result = data['delete'](key)

    this.size = data.size
    return result
  }

  /**
   * Gets the stack value for `key`.
   *
   * @private
   * @name get
   * @memberOf Stack
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function stackGet(key) {
    return this.__data__.get(key)
  }

  /**
   * Checks if a stack value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf Stack
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function stackHas(key) {
    return this.__data__.has(key)
  }

  /** Used to detect overreaching core-js shims. */
  var coreJsData = root['__core-js_shared__']

  /** Used to detect methods masquerading as native. */
  var maskSrcKey = (function() {
    var uid = /[^.]+$/.exec(
      (coreJsData && coreJsData.keys && coreJsData.keys.IE_PROTO) || ''
    )
    return uid ? 'Symbol(src)_1.' + uid : ''
  })()

  /**
   * Checks if `func` has its source masked.
   *
   * @private
   * @param {Function} func The function to check.
   * @returns {boolean} Returns `true` if `func` is masked, else `false`.
   */
  function isMasked(func) {
    return !!maskSrcKey && maskSrcKey in func
  }

  /** Used for built-in method references. */
  var funcProto = Function.prototype

  /** Used to resolve the decompiled source of functions. */
  var funcToString = funcProto.toString

  /**
   * Converts `func` to its source code.
   *
   * @private
   * @param {Function} func The function to convert.
   * @returns {string} Returns the source code.
   */
  function toSource(func) {
    if (func != null) {
      try {
        return funcToString.call(func)
      } catch (e) {}
      try {
        return func + ''
      } catch (e) {}
    }
    return ''
  }

  /**
   * Used to match `RegExp`
   * [syntax characters](http://ecma-international.org/ecma-262/7.0/#sec-patterns).
   */
  var reRegExpChar = /[\\^$.*+?()[\]{}|]/g

  /** Used to detect host constructors (Safari). */
  var reIsHostCtor$1 = /^\[object .+?Constructor\]$/

  /** Used for built-in method references. */
  var funcProto$1 = Function.prototype,
    objectProto$3 = Object.prototype

  /** Used to resolve the decompiled source of functions. */
  var funcToString$1 = funcProto$1.toString

  /** Used to check objects for own properties. */
  var hasOwnProperty$3 = objectProto$3.hasOwnProperty

  /** Used to detect if a method is native. */
  var reIsNative$1 = RegExp(
    '^' +
      funcToString$1
        .call(hasOwnProperty$3)
        .replace(reRegExpChar, '\\$&')
        .replace(
          /hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g,
          '$1.*?'
        ) +
      '$'
  )

  /**
   * The base implementation of `_.isNative` without bad shim checks.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a native function,
   *  else `false`.
   */
  function baseIsNative(value) {
    if (!isObject(value) || isMasked(value)) {
      return false
    }
    var pattern = isFunction(value) ? reIsNative$1 : reIsHostCtor$1
    return pattern.test(toSource(value))
  }

  /**
   * Gets the value at `key` of `object`.
   *
   * @private
   * @param {Object} [object] The object to query.
   * @param {string} key The key of the property to get.
   * @returns {*} Returns the property value.
   */
  function getValue(object, key) {
    return object == null ? undefined : object[key]
  }

  /**
   * Gets the native function at `key` of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {string} key The key of the method to get.
   * @returns {*} Returns the function if it's native, else `undefined`.
   */
  function getNative$1(object, key) {
    var value = getValue(object, key)
    return baseIsNative(value) ? value : undefined
  }

  /* Built-in method references that are verified to be native. */
  var Map$1 = getNative$1(root, 'Map')

  /* Built-in method references that are verified to be native. */
  var nativeCreate = getNative$1(Object, 'create')

  /**
   * Removes all key-value entries from the hash.
   *
   * @private
   * @name clear
   * @memberOf Hash
   */
  function hashClear() {
    this.__data__ = nativeCreate ? nativeCreate(null) : {}
    this.size = 0
  }

  /**
   * Removes `key` and its value from the hash.
   *
   * @private
   * @name delete
   * @memberOf Hash
   * @param {Object} hash The hash to modify.
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function hashDelete(key) {
    var result = this.has(key) && delete this.__data__[key]
    this.size -= result ? 1 : 0
    return result
  }

  /** Used to stand-in for `undefined` hash values. */
  var HASH_UNDEFINED = '__lodash_hash_undefined__'

  /** Used for built-in method references. */
  var objectProto$4 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$4 = objectProto$4.hasOwnProperty

  /**
   * Gets the hash value for `key`.
   *
   * @private
   * @name get
   * @memberOf Hash
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function hashGet(key) {
    var data = this.__data__
    if (nativeCreate) {
      var result = data[key]
      return result === HASH_UNDEFINED ? undefined : result
    }
    return hasOwnProperty$4.call(data, key) ? data[key] : undefined
  }

  /** Used for built-in method references. */
  var objectProto$5 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$5 = objectProto$5.hasOwnProperty

  /**
   * Checks if a hash value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf Hash
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function hashHas(key) {
    var data = this.__data__
    return nativeCreate
      ? data[key] !== undefined
      : hasOwnProperty$5.call(data, key)
  }

  /** Used to stand-in for `undefined` hash values. */
  var HASH_UNDEFINED$1 = '__lodash_hash_undefined__'

  /**
   * Sets the hash `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf Hash
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the hash instance.
   */
  function hashSet(key, value) {
    var data = this.__data__
    this.size += this.has(key) ? 0 : 1
    data[key] = nativeCreate && value === undefined ? HASH_UNDEFINED$1 : value
    return this
  }

  /**
   * Creates a hash object.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function Hash(entries) {
    var index = -1,
      length = entries == null ? 0 : entries.length

    this.clear()
    while (++index < length) {
      var entry = entries[index]
      this.set(entry[0], entry[1])
    }
  }

  // Add methods to `Hash`.
  Hash.prototype.clear = hashClear
  Hash.prototype['delete'] = hashDelete
  Hash.prototype.get = hashGet
  Hash.prototype.has = hashHas
  Hash.prototype.set = hashSet

  /**
   * Removes all key-value entries from the map.
   *
   * @private
   * @name clear
   * @memberOf MapCache
   */
  function mapCacheClear() {
    this.size = 0
    this.__data__ = {
      hash: new Hash(),
      map: new (Map$1 || ListCache)(),
      string: new Hash(),
    }
  }

  /**
   * Checks if `value` is suitable for use as unique object key.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is suitable, else `false`.
   */
  function isKeyable(value) {
    var type = typeof value
    return type == 'string' ||
      type == 'number' ||
      type == 'symbol' ||
      type == 'boolean'
      ? value !== '__proto__'
      : value === null
  }

  /**
   * Gets the data for `map`.
   *
   * @private
   * @param {Object} map The map to query.
   * @param {string} key The reference key.
   * @returns {*} Returns the map data.
   */
  function getMapData(map, key) {
    var data = map.__data__
    return isKeyable(key)
      ? data[typeof key == 'string' ? 'string' : 'hash']
      : data.map
  }

  /**
   * Removes `key` and its value from the map.
   *
   * @private
   * @name delete
   * @memberOf MapCache
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function mapCacheDelete(key) {
    var result = getMapData(this, key)['delete'](key)
    this.size -= result ? 1 : 0
    return result
  }

  /**
   * Gets the map value for `key`.
   *
   * @private
   * @name get
   * @memberOf MapCache
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function mapCacheGet(key) {
    return getMapData(this, key).get(key)
  }

  /**
   * Checks if a map value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf MapCache
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function mapCacheHas(key) {
    return getMapData(this, key).has(key)
  }

  /**
   * Sets the map `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf MapCache
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the map cache instance.
   */
  function mapCacheSet(key, value) {
    var data = getMapData(this, key),
      size = data.size

    data.set(key, value)
    this.size += data.size == size ? 0 : 1
    return this
  }

  /**
   * Creates a map cache object to store key-value pairs.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function MapCache(entries) {
    var index = -1,
      length = entries == null ? 0 : entries.length

    this.clear()
    while (++index < length) {
      var entry = entries[index]
      this.set(entry[0], entry[1])
    }
  }

  // Add methods to `MapCache`.
  MapCache.prototype.clear = mapCacheClear
  MapCache.prototype['delete'] = mapCacheDelete
  MapCache.prototype.get = mapCacheGet
  MapCache.prototype.has = mapCacheHas
  MapCache.prototype.set = mapCacheSet

  /** Used as the size to enable large array optimizations. */
  var LARGE_ARRAY_SIZE = 200

  /**
   * Sets the stack `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf Stack
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the stack cache instance.
   */
  function stackSet(key, value) {
    var data = this.__data__
    if (data instanceof ListCache) {
      var pairs = data.__data__
      if (!Map$1 || pairs.length < LARGE_ARRAY_SIZE - 1) {
        pairs.push([key, value])
        this.size = ++data.size
        return this
      }
      data = this.__data__ = new MapCache(pairs)
    }
    data.set(key, value)
    this.size = data.size
    return this
  }

  /**
   * Creates a stack cache object to store key-value pairs.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function Stack(entries) {
    var data = (this.__data__ = new ListCache(entries))
    this.size = data.size
  }

  // Add methods to `Stack`.
  Stack.prototype.clear = stackClear
  Stack.prototype['delete'] = stackDelete
  Stack.prototype.get = stackGet
  Stack.prototype.has = stackHas
  Stack.prototype.set = stackSet

  /** Used to stand-in for `undefined` hash values. */
  var HASH_UNDEFINED$2 = '__lodash_hash_undefined__'

  /**
   * Adds `value` to the array cache.
   *
   * @private
   * @name add
   * @memberOf SetCache
   * @alias push
   * @param {*} value The value to cache.
   * @returns {Object} Returns the cache instance.
   */
  function setCacheAdd(value) {
    this.__data__.set(value, HASH_UNDEFINED$2)
    return this
  }

  /**
   * Checks if `value` is in the array cache.
   *
   * @private
   * @name has
   * @memberOf SetCache
   * @param {*} value The value to search for.
   * @returns {number} Returns `true` if `value` is found, else `false`.
   */
  function setCacheHas(value) {
    return this.__data__.has(value)
  }

  /**
   *
   * Creates an array cache object to store unique values.
   *
   * @private
   * @constructor
   * @param {Array} [values] The values to cache.
   */
  function SetCache(values) {
    var index = -1,
      length = values == null ? 0 : values.length

    this.__data__ = new MapCache()
    while (++index < length) {
      this.add(values[index])
    }
  }

  // Add methods to `SetCache`.
  SetCache.prototype.add = SetCache.prototype.push = setCacheAdd
  SetCache.prototype.has = setCacheHas

  /**
   * A specialized version of `_.some` for arrays without support for iteratee
   * shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {boolean} Returns `true` if any element passes the predicate check,
   *  else `false`.
   */
  function arraySome(array, predicate) {
    var index = -1,
      length = array == null ? 0 : array.length

    while (++index < length) {
      if (predicate(array[index], index, array)) {
        return true
      }
    }
    return false
  }

  /**
   * Checks if a `cache` value for `key` exists.
   *
   * @private
   * @param {Object} cache The cache to query.
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function cacheHas(cache, key) {
    return cache.has(key)
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG = 1,
    COMPARE_UNORDERED_FLAG = 2

  /**
   * A specialized version of `baseIsEqualDeep` for arrays with support for
   * partial deep comparisons.
   *
   * @private
   * @param {Array} array The array to compare.
   * @param {Array} other The other array to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} stack Tracks traversed `array` and `other` objects.
   * @returns {boolean} Returns `true` if the arrays are equivalent, else `false`.
   */
  function equalArrays(array, other, bitmask, customizer, equalFunc, stack) {
    var isPartial = bitmask & COMPARE_PARTIAL_FLAG,
      arrLength = array.length,
      othLength = other.length

    if (arrLength != othLength && !(isPartial && othLength > arrLength)) {
      return false
    }
    // Assume cyclic values are equal.
    var stacked = stack.get(array)
    if (stacked && stack.get(other)) {
      return stacked == other
    }
    var index = -1,
      result = true,
      seen = bitmask & COMPARE_UNORDERED_FLAG ? new SetCache() : undefined

    stack.set(array, other)
    stack.set(other, array)

    // Ignore non-index properties.
    while (++index < arrLength) {
      var arrValue = array[index],
        othValue = other[index]

      if (customizer) {
        var compared = isPartial
          ? customizer(othValue, arrValue, index, other, array, stack)
          : customizer(arrValue, othValue, index, array, other, stack)
      }
      if (compared !== undefined) {
        if (compared) {
          continue
        }
        result = false
        break
      }
      // Recursively compare arrays (susceptible to call stack limits).
      if (seen) {
        if (
          !arraySome(other, function(othValue, othIndex) {
            if (
              !cacheHas(seen, othIndex) &&
              (arrValue === othValue ||
                equalFunc(arrValue, othValue, bitmask, customizer, stack))
            ) {
              return seen.push(othIndex)
            }
          })
        ) {
          result = false
          break
        }
      } else if (
        !(
          arrValue === othValue ||
          equalFunc(arrValue, othValue, bitmask, customizer, stack)
        )
      ) {
        result = false
        break
      }
    }
    stack['delete'](array)
    stack['delete'](other)
    return result
  }

  /** Built-in value references. */
  var Uint8Array = root.Uint8Array

  /**
   * Converts `map` to its key-value pairs.
   *
   * @private
   * @param {Object} map The map to convert.
   * @returns {Array} Returns the key-value pairs.
   */
  function mapToArray(map) {
    var index = -1,
      result = Array(map.size)

    map.forEach(function(value, key) {
      result[++index] = [key, value]
    })
    return result
  }

  /**
   * Converts `set` to an array of its values.
   *
   * @private
   * @param {Object} set The set to convert.
   * @returns {Array} Returns the values.
   */
  function setToArray(set) {
    var index = -1,
      result = Array(set.size)

    set.forEach(function(value) {
      result[++index] = value
    })
    return result
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$1 = 1,
    COMPARE_UNORDERED_FLAG$1 = 2

  /** `Object#toString` result references. */
  var boolTag = '[object Boolean]',
    dateTag = '[object Date]',
    errorTag = '[object Error]',
    mapTag = '[object Map]',
    numberTag = '[object Number]',
    regexpTag = '[object RegExp]',
    setTag = '[object Set]',
    stringTag = '[object String]',
    symbolTag$1 = '[object Symbol]'

  var arrayBufferTag = '[object ArrayBuffer]',
    dataViewTag = '[object DataView]'

  /** Used to convert symbols to primitives and strings. */
  var symbolProto = Symbol$1 ? Symbol$1.prototype : undefined,
    symbolValueOf = symbolProto ? symbolProto.valueOf : undefined

  /**
   * A specialized version of `baseIsEqualDeep` for comparing objects of
   * the same `toStringTag`.
   *
   * **Note:** This function only supports comparing values with tags of
   * `Boolean`, `Date`, `Error`, `Number`, `RegExp`, or `String`.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {string} tag The `toStringTag` of the objects to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} stack Tracks traversed `object` and `other` objects.
   * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
   */
  function equalByTag(
    object,
    other,
    tag,
    bitmask,
    customizer,
    equalFunc,
    stack
  ) {
    switch (tag) {
      case dataViewTag:
        if (
          object.byteLength != other.byteLength ||
          object.byteOffset != other.byteOffset
        ) {
          return false
        }
        object = object.buffer
        other = other.buffer

      case arrayBufferTag:
        if (
          object.byteLength != other.byteLength ||
          !equalFunc(new Uint8Array(object), new Uint8Array(other))
        ) {
          return false
        }
        return true

      case boolTag:
      case dateTag:
      case numberTag:
        // Coerce booleans to `1` or `0` and dates to milliseconds.
        // Invalid dates are coerced to `NaN`.
        return eq$1(+object, +other)

      case errorTag:
        return object.name == other.name && object.message == other.message

      case regexpTag:
      case stringTag:
        // Coerce regexes to strings and treat strings, primitives and objects,
        // as equal. See http://www.ecma-international.org/ecma-262/7.0/#sec-regexp.prototype.tostring
        // for more details.
        return object == other + ''

      case mapTag:
        var convert = mapToArray

      case setTag:
        var isPartial = bitmask & COMPARE_PARTIAL_FLAG$1
        convert || (convert = setToArray)

        if (object.size != other.size && !isPartial) {
          return false
        }
        // Assume cyclic values are equal.
        var stacked = stack.get(object)
        if (stacked) {
          return stacked == other
        }
        bitmask |= COMPARE_UNORDERED_FLAG$1

        // Recursively compare objects (susceptible to call stack limits).
        stack.set(object, other)
        var result = equalArrays(
          convert(object),
          convert(other),
          bitmask,
          customizer,
          equalFunc,
          stack
        )
        stack['delete'](object)
        return result

      case symbolTag$1:
        if (symbolValueOf) {
          return symbolValueOf.call(object) == symbolValueOf.call(other)
        }
    }
    return false
  }

  /**
   * Appends the elements of `values` to `array`.
   *
   * @private
   * @param {Array} array The array to modify.
   * @param {Array} values The values to append.
   * @returns {Array} Returns `array`.
   */
  function arrayPush(array, values) {
    var index = -1,
      length = values.length,
      offset = array.length

    while (++index < length) {
      array[offset + index] = values[index]
    }
    return array
  }

  /**
   * Checks if `value` is classified as an `Array` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an array, else `false`.
   * @example
   *
   * _.isArray([1, 2, 3]);
   * // => true
   *
   * _.isArray(document.body.children);
   * // => false
   *
   * _.isArray('abc');
   * // => false
   *
   * _.isArray(_.noop);
   * // => false
   */
  var isArray = Array.isArray

  /**
   * The base implementation of `getAllKeys` and `getAllKeysIn` which uses
   * `keysFunc` and `symbolsFunc` to get the enumerable property names and
   * symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Function} keysFunc The function to get the keys of `object`.
   * @param {Function} symbolsFunc The function to get the symbols of `object`.
   * @returns {Array} Returns the array of property names and symbols.
   */
  function baseGetAllKeys(object, keysFunc, symbolsFunc) {
    var result = keysFunc(object)
    return isArray(object) ? result : arrayPush(result, symbolsFunc(object))
  }

  /**
   * A specialized version of `_.filter` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {Array} Returns the new filtered array.
   */
  function arrayFilter(array, predicate) {
    var index = -1,
      length = array == null ? 0 : array.length,
      resIndex = 0,
      result = []

    while (++index < length) {
      var value = array[index]
      if (predicate(value, index, array)) {
        result[resIndex++] = value
      }
    }
    return result
  }

  /**
   * This method returns a new empty array.
   *
   * @static
   * @memberOf _
   * @since 4.13.0
   * @category Util
   * @returns {Array} Returns the new empty array.
   * @example
   *
   * var arrays = _.times(2, _.stubArray);
   *
   * console.log(arrays);
   * // => [[], []]
   *
   * console.log(arrays[0] === arrays[1]);
   * // => false
   */
  function stubArray() {
    return []
  }

  /** Used for built-in method references. */
  var objectProto$6 = Object.prototype

  /** Built-in value references. */
  var propertyIsEnumerable = objectProto$6.propertyIsEnumerable

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeGetSymbols = Object.getOwnPropertySymbols

  /**
   * Creates an array of the own enumerable symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of symbols.
   */
  var getSymbols = !nativeGetSymbols
    ? stubArray
    : function(object) {
        if (object == null) {
          return []
        }
        object = Object(object)
        return arrayFilter(nativeGetSymbols(object), function(symbol) {
          return propertyIsEnumerable.call(object, symbol)
        })
      }

  /**
   * The base implementation of `_.times` without support for iteratee shorthands
   * or max array length checks.
   *
   * @private
   * @param {number} n The number of times to invoke `iteratee`.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the array of results.
   */
  function baseTimes(n, iteratee) {
    var index = -1,
      result = Array(n)

    while (++index < n) {
      result[index] = iteratee(index)
    }
    return result
  }

  /** `Object#toString` result references. */
  var argsTag = '[object Arguments]'

  /**
   * The base implementation of `_.isArguments`.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an `arguments` object,
   */
  function baseIsArguments(value) {
    return isObjectLike(value) && baseGetTag(value) == argsTag
  }

  /** Used for built-in method references. */
  var objectProto$7 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$6 = objectProto$7.hasOwnProperty

  /** Built-in value references. */
  var propertyIsEnumerable$1 = objectProto$7.propertyIsEnumerable

  /**
   * Checks if `value` is likely an `arguments` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an `arguments` object,
   *  else `false`.
   * @example
   *
   * _.isArguments(function() { return arguments; }());
   * // => true
   *
   * _.isArguments([1, 2, 3]);
   * // => false
   */
  var isArguments = baseIsArguments(
    (function() {
      return arguments
    })()
  )
    ? baseIsArguments
    : function(value) {
        return (
          isObjectLike(value) &&
          hasOwnProperty$6.call(value, 'callee') &&
          !propertyIsEnumerable$1.call(value, 'callee')
        )
      }

  /**
   * This method returns `false`.
   *
   * @static
   * @memberOf _
   * @since 4.13.0
   * @category Util
   * @returns {boolean} Returns `false`.
   * @example
   *
   * _.times(2, _.stubFalse);
   * // => [false, false]
   */
  function stubFalse() {
    return false
  }

  /** Detect free variable `exports`. */
  var freeExports =
    typeof exports == 'object' && exports && !exports.nodeType && exports

  /** Detect free variable `module`. */
  var freeModule =
    freeExports &&
    typeof module == 'object' &&
    module &&
    !module.nodeType &&
    module

  /** Detect the popular CommonJS extension `module.exports`. */
  var moduleExports = freeModule && freeModule.exports === freeExports

  /** Built-in value references. */
  var Buffer = moduleExports ? root.Buffer : undefined

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeIsBuffer = Buffer ? Buffer.isBuffer : undefined

  /**
   * Checks if `value` is a buffer.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a buffer, else `false`.
   * @example
   *
   * _.isBuffer(new Buffer(2));
   * // => true
   *
   * _.isBuffer(new Uint8Array(2));
   * // => false
   */
  var isBuffer = nativeIsBuffer || stubFalse

  /** `Object#toString` result references. */
  var argsTag$1 = '[object Arguments]',
    arrayTag = '[object Array]',
    boolTag$1 = '[object Boolean]',
    dateTag$1 = '[object Date]',
    errorTag$1 = '[object Error]',
    funcTag$2 = '[object Function]',
    mapTag$1 = '[object Map]',
    numberTag$1 = '[object Number]',
    objectTag = '[object Object]',
    regexpTag$1 = '[object RegExp]',
    setTag$1 = '[object Set]',
    stringTag$1 = '[object String]',
    weakMapTag = '[object WeakMap]'

  var arrayBufferTag$1 = '[object ArrayBuffer]',
    dataViewTag$1 = '[object DataView]',
    float32Tag = '[object Float32Array]',
    float64Tag = '[object Float64Array]',
    int8Tag = '[object Int8Array]',
    int16Tag = '[object Int16Array]',
    int32Tag = '[object Int32Array]',
    uint8Tag = '[object Uint8Array]',
    uint8ClampedTag = '[object Uint8ClampedArray]',
    uint16Tag = '[object Uint16Array]',
    uint32Tag = '[object Uint32Array]'

  /** Used to identify `toStringTag` values of typed arrays. */
  var typedArrayTags = {}
  typedArrayTags[float32Tag] = typedArrayTags[float64Tag] = typedArrayTags[
    int8Tag
  ] = typedArrayTags[int16Tag] = typedArrayTags[int32Tag] = typedArrayTags[
    uint8Tag
  ] = typedArrayTags[uint8ClampedTag] = typedArrayTags[
    uint16Tag
  ] = typedArrayTags[uint32Tag] = true
  typedArrayTags[argsTag$1] = typedArrayTags[arrayTag] = typedArrayTags[
    arrayBufferTag$1
  ] = typedArrayTags[boolTag$1] = typedArrayTags[
    dataViewTag$1
  ] = typedArrayTags[dateTag$1] = typedArrayTags[errorTag$1] = typedArrayTags[
    funcTag$2
  ] = typedArrayTags[mapTag$1] = typedArrayTags[numberTag$1] = typedArrayTags[
    objectTag
  ] = typedArrayTags[regexpTag$1] = typedArrayTags[setTag$1] = typedArrayTags[
    stringTag$1
  ] = typedArrayTags[weakMapTag] = false

  /**
   * The base implementation of `_.isTypedArray` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
   */
  function baseIsTypedArray(value) {
    return (
      isObjectLike(value) &&
      isLength(value.length) &&
      !!typedArrayTags[baseGetTag(value)]
    )
  }

  /**
   * The base implementation of `_.unary` without support for storing metadata.
   *
   * @private
   * @param {Function} func The function to cap arguments for.
   * @returns {Function} Returns the new capped function.
   */
  function baseUnary(func) {
    return function(value) {
      return func(value)
    }
  }

  /** Detect free variable `exports`. */
  var freeExports$1 =
    typeof exports == 'object' && exports && !exports.nodeType && exports

  /** Detect free variable `module`. */
  var freeModule$1 =
    freeExports$1 &&
    typeof module == 'object' &&
    module &&
    !module.nodeType &&
    module

  /** Detect the popular CommonJS extension `module.exports`. */
  var moduleExports$1 = freeModule$1 && freeModule$1.exports === freeExports$1

  /** Detect free variable `process` from Node.js. */
  var freeProcess = moduleExports$1 && freeGlobal.process

  /** Used to access faster Node.js helpers. */
  var nodeUtil = (function() {
    try {
      // Use `util.types` for Node.js 10+.
      var types =
        freeModule$1 &&
        freeModule$1.require &&
        freeModule$1.require('util').types

      if (types) {
        return types
      }

      // Legacy `process.binding('util')` for Node.js < 10.
      return freeProcess && freeProcess.binding && freeProcess.binding('util')
    } catch (e) {}
  })()

  /* Node.js helper references. */
  var nodeIsTypedArray = nodeUtil && nodeUtil.isTypedArray

  /**
   * Checks if `value` is classified as a typed array.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
   * @example
   *
   * _.isTypedArray(new Uint8Array);
   * // => true
   *
   * _.isTypedArray([]);
   * // => false
   */
  var isTypedArray = nodeIsTypedArray
    ? baseUnary(nodeIsTypedArray)
    : baseIsTypedArray

  /** Used for built-in method references. */
  var objectProto$8 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$7 = objectProto$8.hasOwnProperty

  /**
   * Creates an array of the enumerable property names of the array-like `value`.
   *
   * @private
   * @param {*} value The value to query.
   * @param {boolean} inherited Specify returning inherited property names.
   * @returns {Array} Returns the array of property names.
   */
  function arrayLikeKeys(value, inherited) {
    var isArr = isArray(value),
      isArg = !isArr && isArguments(value),
      isBuff = !isArr && !isArg && isBuffer(value),
      isType = !isArr && !isArg && !isBuff && isTypedArray(value),
      skipIndexes = isArr || isArg || isBuff || isType,
      result = skipIndexes ? baseTimes(value.length, String) : [],
      length = result.length

    for (var key in value) {
      if (
        (inherited || hasOwnProperty$7.call(value, key)) &&
        !(
          skipIndexes &&
          // Safari 9 has enumerable `arguments.length` in strict mode.
          (key == 'length' ||
            // Node.js 0.10 has enumerable non-index properties on buffers.
            (isBuff && (key == 'offset' || key == 'parent')) ||
            // PhantomJS 2 has enumerable non-index properties on typed arrays.
            (isType &&
              (key == 'buffer' ||
                key == 'byteLength' ||
                key == 'byteOffset')) ||
            // Skip index properties.
            isIndex(key, length))
        )
      ) {
        result.push(key)
      }
    }
    return result
  }

  /** Used for built-in method references. */
  var objectProto$9 = Object.prototype

  /**
   * Checks if `value` is likely a prototype object.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a prototype, else `false`.
   */
  function isPrototype(value) {
    var Ctor = value && value.constructor,
      proto = (typeof Ctor == 'function' && Ctor.prototype) || objectProto$9

    return value === proto
  }

  /**
   * Creates a unary function that invokes `func` with its argument transformed.
   *
   * @private
   * @param {Function} func The function to wrap.
   * @param {Function} transform The argument transform.
   * @returns {Function} Returns the new function.
   */
  function overArg(func, transform) {
    return function(arg) {
      return func(transform(arg))
    }
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeKeys = overArg(Object.keys, Object)

  /** Used for built-in method references. */
  var objectProto$a = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$8 = objectProto$a.hasOwnProperty

  /**
   * The base implementation of `_.keys` which doesn't treat sparse arrays as dense.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   */
  function baseKeys(object) {
    if (!isPrototype(object)) {
      return nativeKeys(object)
    }
    var result = []
    for (var key in Object(object)) {
      if (hasOwnProperty$8.call(object, key) && key != 'constructor') {
        result.push(key)
      }
    }
    return result
  }

  /**
   * Creates an array of the own enumerable property names of `object`.
   *
   * **Note:** Non-object values are coerced to objects. See the
   * [ES spec](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
   * for more details.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.keys(new Foo);
   * // => ['a', 'b'] (iteration order is not guaranteed)
   *
   * _.keys('hi');
   * // => ['0', '1']
   */
  function keys(object) {
    return isArrayLike(object) ? arrayLikeKeys(object) : baseKeys(object)
  }

  /**
   * Creates an array of own enumerable property names and symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names and symbols.
   */
  function getAllKeys(object) {
    return baseGetAllKeys(object, keys, getSymbols)
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$2 = 1

  /** Used for built-in method references. */
  var objectProto$b = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$9 = objectProto$b.hasOwnProperty

  /**
   * A specialized version of `baseIsEqualDeep` for objects with support for
   * partial deep comparisons.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} stack Tracks traversed `object` and `other` objects.
   * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
   */
  function equalObjects(object, other, bitmask, customizer, equalFunc, stack) {
    var isPartial = bitmask & COMPARE_PARTIAL_FLAG$2,
      objProps = getAllKeys(object),
      objLength = objProps.length,
      othProps = getAllKeys(other),
      othLength = othProps.length

    if (objLength != othLength && !isPartial) {
      return false
    }
    var index = objLength
    while (index--) {
      var key = objProps[index]
      if (!(isPartial ? key in other : hasOwnProperty$9.call(other, key))) {
        return false
      }
    }
    // Assume cyclic values are equal.
    var stacked = stack.get(object)
    if (stacked && stack.get(other)) {
      return stacked == other
    }
    var result = true
    stack.set(object, other)
    stack.set(other, object)

    var skipCtor = isPartial
    while (++index < objLength) {
      key = objProps[index]
      var objValue = object[key],
        othValue = other[key]

      if (customizer) {
        var compared = isPartial
          ? customizer(othValue, objValue, key, other, object, stack)
          : customizer(objValue, othValue, key, object, other, stack)
      }
      // Recursively compare objects (susceptible to call stack limits).
      if (
        !(compared === undefined
          ? objValue === othValue ||
            equalFunc(objValue, othValue, bitmask, customizer, stack)
          : compared)
      ) {
        result = false
        break
      }
      skipCtor || (skipCtor = key == 'constructor')
    }
    if (result && !skipCtor) {
      var objCtor = object.constructor,
        othCtor = other.constructor

      // Non `Object` object instances with different constructors are not equal.
      if (
        objCtor != othCtor &&
        ('constructor' in object && 'constructor' in other) &&
        !(
          typeof objCtor == 'function' &&
          objCtor instanceof objCtor &&
          typeof othCtor == 'function' &&
          othCtor instanceof othCtor
        )
      ) {
        result = false
      }
    }
    stack['delete'](object)
    stack['delete'](other)
    return result
  }

  /* Built-in method references that are verified to be native. */
  var DataView = getNative$1(root, 'DataView')

  /* Built-in method references that are verified to be native. */
  var Promise = getNative$1(root, 'Promise')

  /* Built-in method references that are verified to be native. */
  var Set = getNative$1(root, 'Set')

  /* Built-in method references that are verified to be native. */
  var WeakMap = getNative$1(root, 'WeakMap')

  /** `Object#toString` result references. */
  var mapTag$2 = '[object Map]',
    objectTag$1 = '[object Object]',
    promiseTag = '[object Promise]',
    setTag$2 = '[object Set]',
    weakMapTag$1 = '[object WeakMap]'

  var dataViewTag$2 = '[object DataView]'

  /** Used to detect maps, sets, and weakmaps. */
  var dataViewCtorString = toSource(DataView),
    mapCtorString = toSource(Map$1),
    promiseCtorString = toSource(Promise),
    setCtorString = toSource(Set),
    weakMapCtorString = toSource(WeakMap)

  /**
   * Gets the `toStringTag` of `value`.
   *
   * @private
   * @param {*} value The value to query.
   * @returns {string} Returns the `toStringTag`.
   */
  var getTag = baseGetTag

  // Fallback for data views, maps, sets, and weak maps in IE 11 and promises in Node.js < 6.
  if (
    (DataView && getTag(new DataView(new ArrayBuffer(1))) != dataViewTag$2) ||
    (Map$1 && getTag(new Map$1()) != mapTag$2) ||
    (Promise && getTag(Promise.resolve()) != promiseTag) ||
    (Set && getTag(new Set()) != setTag$2) ||
    (WeakMap && getTag(new WeakMap()) != weakMapTag$1)
  ) {
    getTag = function(value) {
      var result = baseGetTag(value),
        Ctor = result == objectTag$1 ? value.constructor : undefined,
        ctorString = Ctor ? toSource(Ctor) : ''

      if (ctorString) {
        switch (ctorString) {
          case dataViewCtorString:
            return dataViewTag$2
          case mapCtorString:
            return mapTag$2
          case promiseCtorString:
            return promiseTag
          case setCtorString:
            return setTag$2
          case weakMapCtorString:
            return weakMapTag$1
        }
      }
      return result
    }
  }

  var getTag$1 = getTag

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$3 = 1

  /** `Object#toString` result references. */
  var argsTag$2 = '[object Arguments]',
    arrayTag$1 = '[object Array]',
    objectTag$2 = '[object Object]'

  /** Used for built-in method references. */
  var objectProto$c = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$a = objectProto$c.hasOwnProperty

  /**
   * A specialized version of `baseIsEqual` for arrays and objects which performs
   * deep comparisons and tracks traversed objects enabling objects with circular
   * references to be compared.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} [stack] Tracks traversed `object` and `other` objects.
   * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
   */
  function baseIsEqualDeep(
    object,
    other,
    bitmask,
    customizer,
    equalFunc,
    stack
  ) {
    var objIsArr = isArray(object),
      othIsArr = isArray(other),
      objTag = objIsArr ? arrayTag$1 : getTag$1(object),
      othTag = othIsArr ? arrayTag$1 : getTag$1(other)

    objTag = objTag == argsTag$2 ? objectTag$2 : objTag
    othTag = othTag == argsTag$2 ? objectTag$2 : othTag

    var objIsObj = objTag == objectTag$2,
      othIsObj = othTag == objectTag$2,
      isSameTag = objTag == othTag

    if (isSameTag && isBuffer(object)) {
      if (!isBuffer(other)) {
        return false
      }
      objIsArr = true
      objIsObj = false
    }
    if (isSameTag && !objIsObj) {
      stack || (stack = new Stack())
      return objIsArr || isTypedArray(object)
        ? equalArrays(object, other, bitmask, customizer, equalFunc, stack)
        : equalByTag(
            object,
            other,
            objTag,
            bitmask,
            customizer,
            equalFunc,
            stack
          )
    }
    if (!(bitmask & COMPARE_PARTIAL_FLAG$3)) {
      var objIsWrapped =
          objIsObj && hasOwnProperty$a.call(object, '__wrapped__'),
        othIsWrapped = othIsObj && hasOwnProperty$a.call(other, '__wrapped__')

      if (objIsWrapped || othIsWrapped) {
        var objUnwrapped = objIsWrapped ? object.value() : object,
          othUnwrapped = othIsWrapped ? other.value() : other

        stack || (stack = new Stack())
        return equalFunc(objUnwrapped, othUnwrapped, bitmask, customizer, stack)
      }
    }
    if (!isSameTag) {
      return false
    }
    stack || (stack = new Stack())
    return equalObjects(object, other, bitmask, customizer, equalFunc, stack)
  }

  /**
   * The base implementation of `_.isEqual` which supports partial comparisons
   * and tracks traversed objects.
   *
   * @private
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @param {boolean} bitmask The bitmask flags.
   *  1 - Unordered comparison
   *  2 - Partial comparison
   * @param {Function} [customizer] The function to customize comparisons.
   * @param {Object} [stack] Tracks traversed `value` and `other` objects.
   * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
   */
  function baseIsEqual(value, other, bitmask, customizer, stack) {
    if (value === other) {
      return true
    }
    if (
      value == null ||
      other == null ||
      (!isObjectLike(value) && !isObjectLike(other))
    ) {
      return value !== value && other !== other
    }
    return baseIsEqualDeep(
      value,
      other,
      bitmask,
      customizer,
      baseIsEqual,
      stack
    )
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$4 = 1,
    COMPARE_UNORDERED_FLAG$2 = 2

  /**
   * The base implementation of `_.isMatch` without support for iteratee shorthands.
   *
   * @private
   * @param {Object} object The object to inspect.
   * @param {Object} source The object of property values to match.
   * @param {Array} matchData The property names, values, and compare flags to match.
   * @param {Function} [customizer] The function to customize comparisons.
   * @returns {boolean} Returns `true` if `object` is a match, else `false`.
   */
  function baseIsMatch(object, source, matchData, customizer) {
    var index = matchData.length,
      length = index,
      noCustomizer = !customizer

    if (object == null) {
      return !length
    }
    object = Object(object)
    while (index--) {
      var data = matchData[index]
      if (
        noCustomizer && data[2]
          ? data[1] !== object[data[0]]
          : !(data[0] in object)
      ) {
        return false
      }
    }
    while (++index < length) {
      data = matchData[index]
      var key = data[0],
        objValue = object[key],
        srcValue = data[1]

      if (noCustomizer && data[2]) {
        if (objValue === undefined && !(key in object)) {
          return false
        }
      } else {
        var stack = new Stack()
        if (customizer) {
          var result = customizer(
            objValue,
            srcValue,
            key,
            object,
            source,
            stack
          )
        }
        if (
          !(result === undefined
            ? baseIsEqual(
                srcValue,
                objValue,
                COMPARE_PARTIAL_FLAG$4 | COMPARE_UNORDERED_FLAG$2,
                customizer,
                stack
              )
            : result)
        ) {
          return false
        }
      }
    }
    return true
  }

  /**
   * Checks if `value` is suitable for strict equality comparisons, i.e. `===`.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` if suitable for strict
   *  equality comparisons, else `false`.
   */
  function isStrictComparable(value) {
    return value === value && !isObject(value)
  }

  /**
   * Gets the property names, values, and compare flags of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the match data of `object`.
   */
  function getMatchData(object) {
    var result = keys(object),
      length = result.length

    while (length--) {
      var key = result[length],
        value = object[key]

      result[length] = [key, value, isStrictComparable(value)]
    }
    return result
  }

  /**
   * A specialized version of `matchesProperty` for source values suitable
   * for strict equality comparisons, i.e. `===`.
   *
   * @private
   * @param {string} key The key of the property to get.
   * @param {*} srcValue The value to match.
   * @returns {Function} Returns the new spec function.
   */
  function matchesStrictComparable(key, srcValue) {
    return function(object) {
      if (object == null) {
        return false
      }
      return (
        object[key] === srcValue &&
        (srcValue !== undefined || key in Object(object))
      )
    }
  }

  /**
   * The base implementation of `_.matches` which doesn't clone `source`.
   *
   * @private
   * @param {Object} source The object of property values to match.
   * @returns {Function} Returns the new spec function.
   */
  function baseMatches(source) {
    var matchData = getMatchData(source)
    if (matchData.length == 1 && matchData[0][2]) {
      return matchesStrictComparable(matchData[0][0], matchData[0][1])
    }
    return function(object) {
      return object === source || baseIsMatch(object, source, matchData)
    }
  }

  /** Used to match property names within property paths. */
  var reIsDeepProp = /\.|\[(?:[^[\]]*|(["'])(?:(?!\1)[^\\]|\\.)*?\1)\]/,
    reIsPlainProp = /^\w*$/

  /**
   * Checks if `value` is a property name and not a property path.
   *
   * @private
   * @param {*} value The value to check.
   * @param {Object} [object] The object to query keys on.
   * @returns {boolean} Returns `true` if `value` is a property name, else `false`.
   */
  function isKey(value, object) {
    if (isArray(value)) {
      return false
    }
    var type = typeof value
    if (
      type == 'number' ||
      type == 'symbol' ||
      type == 'boolean' ||
      value == null ||
      isSymbol(value)
    ) {
      return true
    }
    return (
      reIsPlainProp.test(value) ||
      !reIsDeepProp.test(value) ||
      (object != null && value in Object(object))
    )
  }

  /** Error message constants. */
  var FUNC_ERROR_TEXT$2 = 'Expected a function'

  /**
   * Creates a function that memoizes the result of `func`. If `resolver` is
   * provided, it determines the cache key for storing the result based on the
   * arguments provided to the memoized function. By default, the first argument
   * provided to the memoized function is used as the map cache key. The `func`
   * is invoked with the `this` binding of the memoized function.
   *
   * **Note:** The cache is exposed as the `cache` property on the memoized
   * function. Its creation may be customized by replacing the `_.memoize.Cache`
   * constructor with one whose instances implement the
   * [`Map`](http://ecma-international.org/ecma-262/7.0/#sec-properties-of-the-map-prototype-object)
   * method interface of `clear`, `delete`, `get`, `has`, and `set`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to have its output memoized.
   * @param {Function} [resolver] The function to resolve the cache key.
   * @returns {Function} Returns the new memoized function.
   * @example
   *
   * var object = { 'a': 1, 'b': 2 };
   * var other = { 'c': 3, 'd': 4 };
   *
   * var values = _.memoize(_.values);
   * values(object);
   * // => [1, 2]
   *
   * values(other);
   * // => [3, 4]
   *
   * object.a = 2;
   * values(object);
   * // => [1, 2]
   *
   * // Modify the result cache.
   * values.cache.set(object, ['a', 'b']);
   * values(object);
   * // => ['a', 'b']
   *
   * // Replace `_.memoize.Cache`.
   * _.memoize.Cache = WeakMap;
   */
  function memoize(func, resolver) {
    if (
      typeof func != 'function' ||
      (resolver != null && typeof resolver != 'function')
    ) {
      throw new TypeError(FUNC_ERROR_TEXT$2)
    }
    var memoized = function() {
      var args = arguments,
        key = resolver ? resolver.apply(this, args) : args[0],
        cache = memoized.cache

      if (cache.has(key)) {
        return cache.get(key)
      }
      var result = func.apply(this, args)
      memoized.cache = cache.set(key, result) || cache
      return result
    }
    memoized.cache = new (memoize.Cache || MapCache)()
    return memoized
  }

  // Expose `MapCache`.
  memoize.Cache = MapCache

  /** Used as the maximum memoize cache size. */
  var MAX_MEMOIZE_SIZE = 500

  /**
   * A specialized version of `_.memoize` which clears the memoized function's
   * cache when it exceeds `MAX_MEMOIZE_SIZE`.
   *
   * @private
   * @param {Function} func The function to have its output memoized.
   * @returns {Function} Returns the new memoized function.
   */
  function memoizeCapped(func) {
    var result = memoize(func, function(key) {
      if (cache.size === MAX_MEMOIZE_SIZE) {
        cache.clear()
      }
      return key
    })

    var cache = result.cache
    return result
  }

  /** Used to match property names within property paths. */
  var rePropName = /[^.[\]]+|\[(?:(-?\d+(?:\.\d+)?)|(["'])((?:(?!\2)[^\\]|\\.)*?)\2)\]|(?=(?:\.|\[\])(?:\.|\[\]|$))/g

  /** Used to match backslashes in property paths. */
  var reEscapeChar = /\\(\\)?/g

  /**
   * Converts `string` to a property path array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the property path array.
   */
  var stringToPath = memoizeCapped(function(string) {
    var result = []
    if (string.charCodeAt(0) === 46 /* . */) {
      result.push('')
    }
    string.replace(rePropName, function(match, number, quote, subString) {
      result.push(
        quote ? subString.replace(reEscapeChar, '$1') : number || match
      )
    })
    return result
  })

  /**
   * A specialized version of `_.map` for arrays without support for iteratee
   * shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the new mapped array.
   */
  function arrayMap(array, iteratee) {
    var index = -1,
      length = array == null ? 0 : array.length,
      result = Array(length)

    while (++index < length) {
      result[index] = iteratee(array[index], index, array)
    }
    return result
  }

  /** Used as references for various `Number` constants. */
  var INFINITY$1 = 1 / 0

  /** Used to convert symbols to primitives and strings. */
  var symbolProto$1 = Symbol$1 ? Symbol$1.prototype : undefined,
    symbolToString = symbolProto$1 ? symbolProto$1.toString : undefined

  /**
   * The base implementation of `_.toString` which doesn't convert nullish
   * values to empty strings.
   *
   * @private
   * @param {*} value The value to process.
   * @returns {string} Returns the string.
   */
  function baseToString(value) {
    // Exit early for strings to avoid a performance hit in some environments.
    if (typeof value == 'string') {
      return value
    }
    if (isArray(value)) {
      // Recursively convert values (susceptible to call stack limits).
      return arrayMap(value, baseToString) + ''
    }
    if (isSymbol(value)) {
      return symbolToString ? symbolToString.call(value) : ''
    }
    var result = value + ''
    return result == '0' && 1 / value == -INFINITY$1 ? '-0' : result
  }

  /**
   * Converts `value` to a string. An empty string is returned for `null`
   * and `undefined` values. The sign of `-0` is preserved.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {string} Returns the converted string.
   * @example
   *
   * _.toString(null);
   * // => ''
   *
   * _.toString(-0);
   * // => '-0'
   *
   * _.toString([1, 2, 3]);
   * // => '1,2,3'
   */
  function toString(value) {
    return value == null ? '' : baseToString(value)
  }

  /**
   * Casts `value` to a path array if it's not one.
   *
   * @private
   * @param {*} value The value to inspect.
   * @param {Object} [object] The object to query keys on.
   * @returns {Array} Returns the cast property path array.
   */
  function castPath(value, object) {
    if (isArray(value)) {
      return value
    }
    return isKey(value, object) ? [value] : stringToPath(toString(value))
  }

  /** Used as references for various `Number` constants. */
  var INFINITY$2 = 1 / 0

  /**
   * Converts `value` to a string key if it's not a string or symbol.
   *
   * @private
   * @param {*} value The value to inspect.
   * @returns {string|symbol} Returns the key.
   */
  function toKey(value) {
    if (typeof value == 'string' || isSymbol(value)) {
      return value
    }
    var result = value + ''
    return result == '0' && 1 / value == -INFINITY$2 ? '-0' : result
  }

  /**
   * The base implementation of `_.get` without support for default values.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array|string} path The path of the property to get.
   * @returns {*} Returns the resolved value.
   */
  function baseGet(object, path) {
    path = castPath(path, object)

    var index = 0,
      length = path.length

    while (object != null && index < length) {
      object = object[toKey(path[index++])]
    }
    return index && index == length ? object : undefined
  }

  /**
   * Gets the value at `path` of `object`. If the resolved value is
   * `undefined`, the `defaultValue` is returned in its place.
   *
   * @static
   * @memberOf _
   * @since 3.7.0
   * @category Object
   * @param {Object} object The object to query.
   * @param {Array|string} path The path of the property to get.
   * @param {*} [defaultValue] The value returned for `undefined` resolved values.
   * @returns {*} Returns the resolved value.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': 3 } }] };
   *
   * _.get(object, 'a[0].b.c');
   * // => 3
   *
   * _.get(object, ['a', '0', 'b', 'c']);
   * // => 3
   *
   * _.get(object, 'a.b.c', 'default');
   * // => 'default'
   */
  function get(object, path, defaultValue) {
    var result = object == null ? undefined : baseGet(object, path)
    return result === undefined ? defaultValue : result
  }

  /**
   * The base implementation of `_.hasIn` without support for deep paths.
   *
   * @private
   * @param {Object} [object] The object to query.
   * @param {Array|string} key The key to check.
   * @returns {boolean} Returns `true` if `key` exists, else `false`.
   */
  function baseHasIn(object, key) {
    return object != null && key in Object(object)
  }

  /**
   * Checks if `path` exists on `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array|string} path The path to check.
   * @param {Function} hasFunc The function to check properties.
   * @returns {boolean} Returns `true` if `path` exists, else `false`.
   */
  function hasPath(object, path, hasFunc) {
    path = castPath(path, object)

    var index = -1,
      length = path.length,
      result = false

    while (++index < length) {
      var key = toKey(path[index])
      if (!(result = object != null && hasFunc(object, key))) {
        break
      }
      object = object[key]
    }
    if (result || ++index != length) {
      return result
    }
    length = object == null ? 0 : object.length
    return (
      !!length &&
      isLength(length) &&
      isIndex(key, length) &&
      (isArray(object) || isArguments(object))
    )
  }

  /**
   * Checks if `path` is a direct or inherited property of `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The object to query.
   * @param {Array|string} path The path to check.
   * @returns {boolean} Returns `true` if `path` exists, else `false`.
   * @example
   *
   * var object = _.create({ 'a': _.create({ 'b': 2 }) });
   *
   * _.hasIn(object, 'a');
   * // => true
   *
   * _.hasIn(object, 'a.b');
   * // => true
   *
   * _.hasIn(object, ['a', 'b']);
   * // => true
   *
   * _.hasIn(object, 'b');
   * // => false
   */
  function hasIn(object, path) {
    return object != null && hasPath(object, path, baseHasIn)
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$5 = 1,
    COMPARE_UNORDERED_FLAG$3 = 2

  /**
   * The base implementation of `_.matchesProperty` which doesn't clone `srcValue`.
   *
   * @private
   * @param {string} path The path of the property to get.
   * @param {*} srcValue The value to match.
   * @returns {Function} Returns the new spec function.
   */
  function baseMatchesProperty(path, srcValue) {
    if (isKey(path) && isStrictComparable(srcValue)) {
      return matchesStrictComparable(toKey(path), srcValue)
    }
    return function(object) {
      var objValue = get(object, path)
      return objValue === undefined && objValue === srcValue
        ? hasIn(object, path)
        : baseIsEqual(
            srcValue,
            objValue,
            COMPARE_PARTIAL_FLAG$5 | COMPARE_UNORDERED_FLAG$3
          )
    }
  }

  /**
   * This method returns the first argument it receives.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {*} value Any value.
   * @returns {*} Returns `value`.
   * @example
   *
   * var object = { 'a': 1 };
   *
   * console.log(_.identity(object) === object);
   * // => true
   */
  function identity(value) {
    return value
  }

  /**
   * The base implementation of `_.property` without support for deep paths.
   *
   * @private
   * @param {string} key The key of the property to get.
   * @returns {Function} Returns the new accessor function.
   */
  function baseProperty(key) {
    return function(object) {
      return object == null ? undefined : object[key]
    }
  }

  /**
   * A specialized version of `baseProperty` which supports deep paths.
   *
   * @private
   * @param {Array|string} path The path of the property to get.
   * @returns {Function} Returns the new accessor function.
   */
  function basePropertyDeep(path) {
    return function(object) {
      return baseGet(object, path)
    }
  }

  /**
   * Creates a function that returns the value at `path` of a given object.
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Util
   * @param {Array|string} path The path of the property to get.
   * @returns {Function} Returns the new accessor function.
   * @example
   *
   * var objects = [
   *   { 'a': { 'b': 2 } },
   *   { 'a': { 'b': 1 } }
   * ];
   *
   * _.map(objects, _.property('a.b'));
   * // => [2, 1]
   *
   * _.map(_.sortBy(objects, _.property(['a', 'b'])), 'a.b');
   * // => [1, 2]
   */
  function property(path) {
    return isKey(path) ? baseProperty(toKey(path)) : basePropertyDeep(path)
  }

  /**
   * The base implementation of `_.iteratee`.
   *
   * @private
   * @param {*} [value=_.identity] The value to convert to an iteratee.
   * @returns {Function} Returns the iteratee.
   */
  function baseIteratee(value) {
    // Don't store the `typeof` result in a variable to avoid a JIT bug in Safari 9.
    // See https://bugs.webkit.org/show_bug.cgi?id=156034 for more details.
    if (typeof value == 'function') {
      return value
    }
    if (value == null) {
      return identity
    }
    if (typeof value == 'object') {
      return isArray(value)
        ? baseMatchesProperty(value[0], value[1])
        : baseMatches(value)
    }
    return property(value)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$2 = Math.max

  /**
   * This method is like `_.find` except that it returns the index of the first
   * element `predicate` returns truthy for instead of the element itself.
   *
   * @static
   * @memberOf _
   * @since 1.1.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @param {number} [fromIndex=0] The index to search from.
   * @returns {number} Returns the index of the found element, else `-1`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'active': false },
   *   { 'user': 'fred',    'active': false },
   *   { 'user': 'pebbles', 'active': true }
   * ];
   *
   * _.findIndex(users, function(o) { return o.user == 'barney'; });
   * // => 0
   *
   * // The `_.matches` iteratee shorthand.
   * _.findIndex(users, { 'user': 'fred', 'active': false });
   * // => 1
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.findIndex(users, ['active', false]);
   * // => 0
   *
   * // The `_.property` iteratee shorthand.
   * _.findIndex(users, 'active');
   * // => 2
   */
  function findIndex(array, predicate, fromIndex) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return -1
    }
    var index = fromIndex == null ? 0 : toInteger(fromIndex)
    if (index < 0) {
      index = nativeMax$2(length + index, 0)
    }
    return baseFindIndex(array, baseIteratee(predicate, 3), index)
  }

  function endOfRange(dateRange, unit) {
    if (unit === void 0) {
      unit = 'day'
    }

    return {
      first: dateRange[0],
      last: add(dateRange[dateRange.length - 1], 1, unit),
    }
  }
  function eventSegments(event, range, accessors) {
    var _endOfRange = endOfRange(range),
      first = _endOfRange.first,
      last = _endOfRange.last

    var slots = diff(first, last, 'day')
    var start = max(startOf(accessors.start(event), 'day'), first)
    var end = min(ceil(accessors.end(event), 'day'), last)
    var padding = findIndex(range, function(x) {
      return eq(x, start, 'day')
    })
    var span = diff(start, end, 'day')
    span = Math.min(span, slots)
    span = Math.max(span, 1)
    return {
      event: event,
      span: span,
      left: padding + 1,
      right: Math.max(padding + span, 1),
    }
  }
  function eventLevels(rowSegments, limit) {
    if (limit === void 0) {
      limit = Infinity
    }

    var i,
      j,
      seg,
      levels = [],
      extra = []

    for (i = 0; i < rowSegments.length; i++) {
      seg = rowSegments[i]

      for (j = 0; j < levels.length; j++) {
        if (!segsOverlap(seg, levels[j])) break
      }

      if (j >= limit) {
        extra.push(seg)
      } else {
        ;(levels[j] || (levels[j] = [])).push(seg)
      }
    }

    for (i = 0; i < levels.length; i++) {
      levels[i].sort(function(a, b) {
        return a.left - b.left
      }) //eslint-disable-line
    }

    return {
      levels: levels,
      extra: extra,
    }
  }
  function inRange$1(e, start, end, accessors) {
    var eStart = startOf(accessors.start(e), 'day')
    var eEnd = accessors.end(e)
    var startsBeforeEnd = lte(eStart, end, 'day') // when the event is zero duration we need to handle a bit differently

    var endsAfterStart = !eq(eStart, eEnd, 'minutes')
      ? gt(eEnd, start, 'minutes')
      : gte(eEnd, start, 'minutes')
    return startsBeforeEnd && endsAfterStart
  }
  function segsOverlap(seg, otherSegs) {
    return otherSegs.some(function(otherSeg) {
      return otherSeg.left <= seg.right && otherSeg.right >= seg.left
    })
  }
  function sortEvents(evtA, evtB, accessors) {
    var startSort =
      +startOf(accessors.start(evtA), 'day') -
      +startOf(accessors.start(evtB), 'day')
    var durA = diff(
      accessors.start(evtA),
      ceil(accessors.end(evtA), 'day'),
      'day'
    )
    var durB = diff(
      accessors.start(evtB),
      ceil(accessors.end(evtB), 'day'),
      'day'
    )
    return (
      startSort || // sort by start Day first
      Math.max(durB, 1) - Math.max(durA, 1) || // events spanning multiple days go first
      !!accessors.allDay(evtB) - !!accessors.allDay(evtA) || // then allDay single day events
      +accessors.start(evtA) - +accessors.start(evtB)
    ) // then sort by start time
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeCeil$1 = Math.ceil,
    nativeMax$3 = Math.max

  /**
   * The base implementation of `_.range` and `_.rangeRight` which doesn't
   * coerce arguments.
   *
   * @private
   * @param {number} start The start of the range.
   * @param {number} end The end of the range.
   * @param {number} step The value to increment or decrement by.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Array} Returns the range of numbers.
   */
  function baseRange(start, end, step, fromRight) {
    var index = -1,
      length = nativeMax$3(nativeCeil$1((end - start) / (step || 1)), 0),
      result = Array(length)

    while (length--) {
      result[fromRight ? length : ++index] = start
      start += step
    }
    return result
  }

  /**
   * Creates a `_.range` or `_.rangeRight` function.
   *
   * @private
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Function} Returns the new range function.
   */
  function createRange(fromRight) {
    return function(start, end, step) {
      if (step && typeof step != 'number' && isIterateeCall(start, end, step)) {
        end = step = undefined
      }
      // Ensure the sign of `-0` is preserved.
      start = toFinite(start)
      if (end === undefined) {
        end = start
        start = 0
      } else {
        end = toFinite(end)
      }
      step = step === undefined ? (start < end ? 1 : -1) : toFinite(step)
      return baseRange(start, end, step, fromRight)
    }
  }

  /**
   * Creates an array of numbers (positive and/or negative) progressing from
   * `start` up to, but not including, `end`. A step of `-1` is used if a negative
   * `start` is specified without an `end` or `step`. If `end` is not specified,
   * it's set to `start` with `start` then set to `0`.
   *
   * **Note:** JavaScript follows the IEEE-754 standard for resolving
   * floating-point values which can produce unexpected results.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {number} [start=0] The start of the range.
   * @param {number} end The end of the range.
   * @param {number} [step=1] The value to increment or decrement by.
   * @returns {Array} Returns the range of numbers.
   * @see _.inRange, _.rangeRight
   * @example
   *
   * _.range(4);
   * // => [0, 1, 2, 3]
   *
   * _.range(-4);
   * // => [0, -1, -2, -3]
   *
   * _.range(1, 5);
   * // => [1, 2, 3, 4]
   *
   * _.range(0, 20, 5);
   * // => [0, 5, 10, 15]
   *
   * _.range(0, -4, -1);
   * // => [0, -1, -2, -3]
   *
   * _.range(1, 4, 0);
   * // => [1, 1, 1]
   *
   * _.range(0);
   * // => []
   */
  var range$1 = createRange()

  var isSegmentInSlot = function isSegmentInSlot(seg, slot) {
    return seg.left <= slot && seg.right >= slot
  }

  var eventsInSlot = function eventsInSlot(segments, slot) {
    return segments.filter(function(seg) {
      return isSegmentInSlot(seg, slot)
    }).length
  }

  var EventEndingRow =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(EventEndingRow, _React$Component)

      function EventEndingRow() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = EventEndingRow.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          segments = _this$props.segments,
          slots = _this$props.slotMetrics.slots
        var rowSegments = eventLevels(segments).levels[0]
        var current = 1,
          lastEnd = 1,
          row = []

        while (current <= slots) {
          var key = '_lvl_' + current

          var _ref =
              rowSegments.filter(function(seg) {
                return isSegmentInSlot(seg, current)
              })[0] || {},
            event = _ref.event,
            left = _ref.left,
            right = _ref.right,
            span = _ref.span //eslint-disable-line

          if (!event) {
            current++
            continue
          }

          var gap = Math.max(0, left - lastEnd)

          if (this.canRenderSlotEvent(left, span)) {
            var content = EventRowMixin.renderEvent(this.props, event)

            if (gap) {
              row.push(EventRowMixin.renderSpan(slots, gap, key + '_gap'))
            }

            row.push(EventRowMixin.renderSpan(slots, span, key, content))
            lastEnd = current = right + 1
          } else {
            if (gap) {
              row.push(EventRowMixin.renderSpan(slots, gap, key + '_gap'))
            }

            row.push(
              EventRowMixin.renderSpan(
                slots,
                1,
                key,
                this.renderShowMore(segments, current)
              )
            )
            lastEnd = current = current + 1
          }
        }

        return React__default.createElement(
          'div',
          {
            className: 'rbc-row',
          },
          row
        )
      }

      _proto.canRenderSlotEvent = function canRenderSlotEvent(slot, span) {
        var segments = this.props.segments
        return range$1(slot, slot + span).every(function(s) {
          var count = eventsInSlot(segments, s)
          return count === 1
        })
      }

      _proto.renderShowMore = function renderShowMore(segments, slot) {
        var _this = this

        var _this$props2 = this.props,
          localizer = _this$props2.localizer,
          renderPopover = _this$props2.renderPopover
        var count = eventsInSlot(segments, slot)

        if (!count) {
          return false
        }

        return renderPopover(
          React__default.createElement(
            'a',
            {
              key: 'sm_' + slot,
              href: '#',
              className: 'rbc-show-more',
              onClick: function onClick(e) {
                return _this.showMore(slot, e)
              },
            },
            localizer.messages.showMore(count)
          )
        )
      }

      _proto.showMore = function showMore(slot, e) {
        e.preventDefault()
        this.props.onShowMore(slot)
      }

      return EventEndingRow
    })(React__default.Component)

  EventEndingRow.propTypes = _extends(
    {
      segments: propTypes.array,
      slots: propTypes.number,
      onShowMore: propTypes.func,
    },
    EventRowMixin.propTypes
  )
  EventEndingRow.defaultProps = _extends({}, EventRowMixin.defaultProps)

  var ScrollableWeekWrapper = function ScrollableWeekWrapper(_ref) {
    var children = _ref.children
    return React__default.createElement(
      'div',
      {
        className: 'rbc-row-content-scroll-container',
      },
      children
    )
  }

  function areInputsEqual(newInputs, lastInputs) {
    if (newInputs.length !== lastInputs.length) {
      return false
    }
    for (var i = 0; i < newInputs.length; i++) {
      if (newInputs[i] !== lastInputs[i]) {
        return false
      }
    }
    return true
  }

  function memoizeOne(resultFn, isEqual) {
    if (isEqual === void 0) {
      isEqual = areInputsEqual
    }
    var lastThis
    var lastArgs = []
    var lastResult
    var calledOnce = false
    function memoized() {
      var newArgs = []
      for (var _i = 0; _i < arguments.length; _i++) {
        newArgs[_i] = arguments[_i]
      }
      if (calledOnce && lastThis === this && isEqual(newArgs, lastArgs)) {
        return lastResult
      }
      lastResult = resultFn.apply(this, newArgs)
      calledOnce = true
      lastThis = this
      lastArgs = newArgs
      return lastResult
    }
    return memoized
  }

  var isSegmentInSlot$1 = function isSegmentInSlot(seg, slot) {
    return seg.left <= slot && seg.right >= slot
  }

  var isEqual = function isEqual(a, b) {
    return a[0].range === b[0].range && a[0].events === b[0].events
  }

  function getSlotMetrics() {
    return memoizeOne(function(options) {
      var range = options.range,
        events = options.events,
        maxRows = options.maxRows,
        minRows = options.minRows,
        accessors = options.accessors

      var _endOfRange = endOfRange(range),
        first = _endOfRange.first,
        last = _endOfRange.last

      var segments = events.map(function(evt) {
        return eventSegments(evt, range, accessors)
      })

      var _eventLevels = eventLevels(segments, Math.max(maxRows - 1, 1)),
        levels = _eventLevels.levels,
        extra = _eventLevels.extra

      while (levels.length < minRows) {
        levels.push([])
      }

      return {
        first: first,
        last: last,
        levels: levels,
        extra: extra,
        range: range,
        slots: range.length,
        clone: function clone(args) {
          var metrics = getSlotMetrics()
          return metrics(_extends({}, options, args))
        },
        getDateForSlot: function getDateForSlot(slotNumber) {
          return range[slotNumber]
        },
        getSlotForDate: function getSlotForDate(date) {
          return range.find(function(r) {
            return eq(r, date, 'day')
          })
        },
        getEventsForSlot: function getEventsForSlot(slot) {
          return segments
            .filter(function(seg) {
              return isSegmentInSlot$1(seg, slot)
            })
            .map(function(seg) {
              return seg.event
            })
        },
        continuesPrior: function continuesPrior(event) {
          return lt(accessors.start(event), first, 'day')
        },
        continuesAfter: function continuesAfter(event) {
          var eventEnd = accessors.end(event)
          var singleDayDuration = eq(
            accessors.start(event),
            eventEnd,
            'minutes'
          )
          return singleDayDuration
            ? gte(eventEnd, last, 'minutes')
            : gt(eventEnd, last, 'minutes')
        },
      }
    }, isEqual)
  }

  var DateContentRow =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(DateContentRow, _React$Component)

      function DateContentRow() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(args)) ||
          this

        _this.handleSelectSlot = function(slot) {
          var _this$props = _this.props,
            range = _this$props.range,
            onSelectSlot = _this$props.onSelectSlot
          onSelectSlot(range.slice(slot.start, slot.end + 1), slot)
        }

        _this.handleShowMore = function(slot) {
          var _this$props2 = _this.props,
            range = _this$props2.range,
            onShowMore = _this$props2.onShowMore

          var metrics = _this.slotMetrics(_this.props)

          var row = qsa(
            reactDom.findDOMNode(_assertThisInitialized(_this)),
            '.rbc-row-bg'
          )[0]
          var cell
          if (row) cell = row.children[slot - 1]
          var events = metrics.getEventsForSlot(slot)
          onShowMore(events, range[slot - 1], cell, slot)
        }

        _this.createHeadingRef = function(r) {
          _this.headingRow = r
        }

        _this.createEventRef = function(r) {
          _this.eventRow = r
        }

        _this.getContainer = function() {
          var container = _this.props.container
          return container
            ? container()
            : reactDom.findDOMNode(_assertThisInitialized(_this))
        }

        _this.renderHeadingCell = function(date, index) {
          var _this$props3 = _this.props,
            renderHeader = _this$props3.renderHeader,
            getNow = _this$props3.getNow
          return renderHeader({
            date: date,
            key: 'header_' + index,
            className: clsx(
              'rbc-date-cell',
              eq(date, getNow(), 'day') && 'rbc-now'
            ),
          })
        }

        _this.renderDummy = function() {
          var _this$props4 = _this.props,
            className = _this$props4.className,
            range = _this$props4.range,
            renderHeader = _this$props4.renderHeader,
            showAllEvents = _this$props4.showAllEvents
          return React__default.createElement(
            'div',
            {
              className: className,
            },
            React__default.createElement(
              'div',
              {
                className: clsx(
                  'rbc-row-content',
                  showAllEvents && 'rbc-row-content-scrollable'
                ),
              },
              renderHeader &&
                React__default.createElement(
                  'div',
                  {
                    className: 'rbc-row',
                    ref: _this.createHeadingRef,
                  },
                  range.map(_this.renderHeadingCell)
                ),
              React__default.createElement(
                'div',
                {
                  className: 'rbc-row',
                  ref: _this.createEventRef,
                },
                React__default.createElement(
                  'div',
                  {
                    className: 'rbc-row-segment',
                  },
                  React__default.createElement(
                    'div',
                    {
                      className: 'rbc-event',
                    },
                    React__default.createElement(
                      'div',
                      {
                        className: 'rbc-event-content',
                      },
                      '\xA0'
                    )
                  )
                )
              )
            )
          )
        }

        _this.slotMetrics = getSlotMetrics()
        return _this
      }

      var _proto = DateContentRow.prototype

      _proto.getRowLimit = function getRowLimit() {
        var eventHeight = height(this.eventRow)
        var headingHeight = this.headingRow ? height(this.headingRow) : 0
        var eventSpace = height(reactDom.findDOMNode(this)) - headingHeight
        return Math.max(Math.floor(eventSpace / eventHeight), 1)
      }

      _proto.render = function render() {
        var _this$props5 = this.props,
          date = _this$props5.date,
          rtl = _this$props5.rtl,
          range = _this$props5.range,
          className = _this$props5.className,
          selected = _this$props5.selected,
          selectable = _this$props5.selectable,
          renderForMeasure = _this$props5.renderForMeasure,
          accessors = _this$props5.accessors,
          getters = _this$props5.getters,
          components = _this$props5.components,
          getNow = _this$props5.getNow,
          renderHeader = _this$props5.renderHeader,
          onSelect = _this$props5.onSelect,
          localizer = _this$props5.localizer,
          onSelectStart = _this$props5.onSelectStart,
          onSelectEnd = _this$props5.onSelectEnd,
          onDoubleClick = _this$props5.onDoubleClick,
          onKeyPress = _this$props5.onKeyPress,
          resourceId = _this$props5.resourceId,
          longPressThreshold = _this$props5.longPressThreshold,
          isAllDay = _this$props5.isAllDay,
          resizable = _this$props5.resizable,
          showAllEvents = _this$props5.showAllEvents,
          renderPopover = _this$props5.renderPopover
        if (renderForMeasure) return this.renderDummy()
        var metrics = this.slotMetrics(this.props)
        var levels = metrics.levels,
          extra = metrics.extra
        var ScrollableWeekComponent = showAllEvents
          ? ScrollableWeekWrapper
          : NoopWrapper
        var WeekWrapper = components.weekWrapper
        var eventRowProps = {
          selected: selected,
          accessors: accessors,
          getters: getters,
          localizer: localizer,
          components: components,
          onSelect: onSelect,
          onDoubleClick: onDoubleClick,
          onKeyPress: onKeyPress,
          resourceId: resourceId,
          slotMetrics: metrics,
          resizable: resizable,
        }
        return React__default.createElement(
          'div',
          {
            className: className,
            role: 'rowgroup',
          },
          React__default.createElement(BackgroundCells, {
            date: date,
            getNow: getNow,
            rtl: rtl,
            range: range,
            selectable: selectable,
            container: this.getContainer,
            getters: getters,
            onSelectStart: onSelectStart,
            onSelectEnd: onSelectEnd,
            onSelectSlot: this.handleSelectSlot,
            components: components,
            longPressThreshold: longPressThreshold,
            resourceId: resourceId,
          }),
          React__default.createElement(
            'div',
            {
              className: clsx(
                'rbc-row-content',
                showAllEvents && 'rbc-row-content-scrollable'
              ),
              role: 'row',
            },
            renderHeader &&
              React__default.createElement(
                'div',
                {
                  className: 'rbc-row ',
                  ref: this.createHeadingRef,
                },
                range.map(this.renderHeadingCell)
              ),
            React__default.createElement(
              ScrollableWeekComponent,
              null,
              React__default.createElement(
                WeekWrapper,
                _extends(
                  {
                    isAllDay: isAllDay,
                  },
                  eventRowProps
                ),
                levels.map(function(segs, idx) {
                  return React__default.createElement(
                    EventRow,
                    _extends(
                      {
                        key: idx,
                        segments: segs,
                      },
                      eventRowProps
                    )
                  )
                }),
                !!extra.length &&
                  React__default.createElement(
                    EventEndingRow,
                    _extends(
                      {
                        segments: extra,
                        onShowMore: this.handleShowMore,
                        renderPopover: renderPopover,
                      },
                      eventRowProps
                    )
                  )
              )
            )
          )
        )
      }

      return DateContentRow
    })(React__default.Component)

  DateContentRow.propTypes = {
    date: propTypes.instanceOf(Date),
    events: propTypes.array.isRequired,
    range: propTypes.array.isRequired,
    rtl: propTypes.bool,
    resizable: propTypes.bool,
    resourceId: propTypes.any,
    renderForMeasure: propTypes.bool,
    renderHeader: propTypes.func,
    container: propTypes.func,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onShowMore: propTypes.func,
    showAllEvents: propTypes.bool,
    onSelectSlot: propTypes.func,
    onSelect: propTypes.func,
    onSelectEnd: propTypes.func,
    onSelectStart: propTypes.func,
    onDoubleClick: propTypes.func,
    onKeyPress: propTypes.func,
    dayPropGetter: propTypes.func,
    getNow: propTypes.func.isRequired,
    isAllDay: propTypes.bool,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    minRows: propTypes.number.isRequired,
    maxRows: propTypes.number.isRequired,
    renderPopover: propTypes.func,
  }
  DateContentRow.defaultProps = {
    minRows: 0,
    maxRows: Infinity,
  }

  var Header = function Header(_ref) {
    var label = _ref.label
    return React__default.createElement(
      'span',
      {
        role: 'columnheader',
        'aria-sort': 'none',
      },
      label
    )
  }

  Header.propTypes = {
    label: propTypes.node,
  }

  var DateHeader = function DateHeader(_ref) {
    var label = _ref.label,
      drilldownView = _ref.drilldownView,
      onDrillDown = _ref.onDrillDown

    if (!drilldownView) {
      return React__default.createElement('span', null, label)
    }

    return React__default.createElement(
      'a',
      {
        href: '#',
        onClick: onDrillDown,
        role: 'cell',
      },
      label
    )
  }

  DateHeader.propTypes = {
    label: propTypes.node,
    date: propTypes.instanceOf(Date),
    drilldownView: propTypes.string,
    onDrillDown: propTypes.func,
    isOffRange: propTypes.bool,
  }

  var eventsForWeek = function eventsForWeek(evts, start, end, accessors) {
    return evts.filter(function(e) {
      return inRange$1(e, start, end, accessors)
    })
  }

  var MonthView =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(MonthView, _React$Component)

      function MonthView() {
        var _this

        for (
          var _len = arguments.length, _args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          _args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(_args)) ||
          this

        _this.getContainer = function() {
          return reactDom.findDOMNode(_assertThisInitialized(_this))
        }

        _this.renderWeek = function(week, weekIdx) {
          var _this$props = _this.props,
            events = _this$props.events,
            components = _this$props.components,
            selectable = _this$props.selectable,
            getNow = _this$props.getNow,
            selected = _this$props.selected,
            date = _this$props.date,
            localizer = _this$props.localizer,
            longPressThreshold = _this$props.longPressThreshold,
            accessors = _this$props.accessors,
            getters = _this$props.getters,
            showAllEvents = _this$props.showAllEvents
          var _this$state = _this.state,
            needLimitMeasure = _this$state.needLimitMeasure,
            rowLimit = _this$state.rowLimit
          events = eventsForWeek(
            events,
            week[0],
            week[week.length - 1],
            accessors
          )
          events.sort(function(a, b) {
            return sortEvents(a, b, accessors)
          })
          return React__default.createElement(DateContentRow, {
            key: weekIdx,
            ref: weekIdx === 0 ? _this.slotRowRef : undefined,
            container: _this.getContainer,
            className: 'rbc-month-row',
            getNow: getNow,
            date: date,
            range: week,
            events: events,
            maxRows: showAllEvents ? Infinity : rowLimit,
            selected: selected,
            selectable: selectable,
            components: components,
            accessors: accessors,
            getters: getters,
            localizer: localizer,
            renderHeader: _this.readerDateHeading,
            renderForMeasure: needLimitMeasure,
            onShowMore: _this.handleShowMore,
            renderPopover: _this.renderPopover,
            onSelect: _this.handleSelectEvent,
            onDoubleClick: _this.handleDoubleClickEvent,
            onKeyPress: _this.handleKeyPressEvent,
            onSelectSlot: _this.handleSelectSlot,
            longPressThreshold: longPressThreshold,
            rtl: _this.props.rtl,
            resizable: _this.props.resizable,
            showAllEvents: showAllEvents,
          })
        }

        _this.readerDateHeading = function(_ref) {
          var date = _ref.date,
            className = _ref.className,
            props = _objectWithoutPropertiesLoose(_ref, ['date', 'className'])

          var _this$props2 = _this.props,
            currentDate = _this$props2.date,
            getDrilldownView = _this$props2.getDrilldownView,
            localizer = _this$props2.localizer
          var isOffRange = month(date) !== month(currentDate)
          var isCurrent = eq(date, currentDate, 'day')
          var drilldownView = getDrilldownView(date)
          var label = localizer.format(date, 'dateFormat')
          var DateHeaderComponent =
            _this.props.components.dateHeader || DateHeader
          return React__default.createElement(
            'div',
            _extends({}, props, {
              className: clsx(
                className,
                isOffRange && 'rbc-off-range',
                isCurrent && 'rbc-current'
              ),
              role: 'cell',
            }),
            React__default.createElement(DateHeaderComponent, {
              label: label,
              date: date,
              drilldownView: drilldownView,
              isOffRange: isOffRange,
              onDrillDown: function onDrillDown(e) {
                return _this.handleHeadingClick(date, drilldownView, e)
              },
            })
          )
        }

        _this.renderPopover = function(showMore) {
          var popover = (_this.state && _this.state.popover) || {}

          var _this$props3 = _this.props,
            accessors = _this$props3.accessors,
            localizer = _this$props3.localizer,
            components = _this$props3.components,
            getters = _this$props3.getters,
            selected = _this$props3.selected,
            popupOffset = _this$props3.popupOffset,
            restProps = _objectWithoutPropertiesLoose(_this$props3, [
              'accessors',
              'localizer',
              'components',
              'getters',
              'selected',
              'popupOffset',
            ])

          return React__default.createElement(
            reactPopover,
            {
              preferPlace: 'above',
              isOpen: popover.visible,
              onOuterAction: _this.hidePopover,
              body: React__default.createElement(
                Popup,
                _extends({}, restProps, {
                  popupOffset: popupOffset,
                  accessors: accessors,
                  getters: getters,
                  selected: selected,
                  components: components,
                  localizer: localizer,
                  show: _this.hidePopover,
                  events: popover.events,
                  slotStart: popover.date,
                  slotEnd: popover.end,
                  onSelect: _this.handleSelectEvent,
                  onDoubleClick: _this.handleDoubleClickEvent,
                  onKeyPress: _this.handleKeyPressEvent,
                  handleDragStart: _this.props.handleDragStart,
                })
              ),
            },
            showMore
          )
        }

        _this.handleSelectSlot = function(range, slotInfo) {
          _this._pendingSelection = _this._pendingSelection.concat(range)
          clearTimeout(_this._selectTimer)
          _this._selectTimer = setTimeout(function() {
            return _this.selectDates(slotInfo)
          })
        }

        _this.handleHeadingClick = function(date, view, e) {
          e.preventDefault()

          _this.clearSelection()

          notify(_this.props.onDrillDown, [date, view])
        }

        _this.handleSelectEvent = function() {
          _this.clearSelection()

          for (
            var _len2 = arguments.length, args = new Array(_len2), _key2 = 0;
            _key2 < _len2;
            _key2++
          ) {
            args[_key2] = arguments[_key2]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this.handleDoubleClickEvent = function() {
          _this.clearSelection()

          for (
            var _len3 = arguments.length, args = new Array(_len3), _key3 = 0;
            _key3 < _len3;
            _key3++
          ) {
            args[_key3] = arguments[_key3]
          }

          notify(_this.props.onDoubleClickEvent, args)
        }

        _this.handleKeyPressEvent = function() {
          _this.clearSelection()

          for (
            var _len4 = arguments.length, args = new Array(_len4), _key4 = 0;
            _key4 < _len4;
            _key4++
          ) {
            args[_key4] = arguments[_key4]
          }

          notify(_this.props.onKeyPressEvent, args)
        }

        _this.handleShowMore = function(events, date, cell, slot) {
          var _this$props4 = _this.props,
            popup = _this$props4.popup,
            onDrillDown = _this$props4.onDrillDown,
            onShowMore = _this$props4.onShowMore,
            getDrilldownView = _this$props4.getDrilldownView //cancel any pending selections so only the event click goes through.

          _this.clearSelection()

          if (popup) {
            _this.setState({
              popover: {
                visible: true,
                date: date,
                events: events,
              },
            })
          } else {
            notify(onDrillDown, [date, getDrilldownView(date) || views.DAY])
          }

          notify(onShowMore, [events, date, slot])
        }

        _this.hidePopover = function() {
          _this.setState({
            popover: null,
          })
        }

        _this._bgRows = []
        _this._pendingSelection = []
        _this.slotRowRef = React__default.createRef()
        _this.state = {
          rowLimit: 5,
          needLimitMeasure: true,
        }
        return _this
      }

      var _proto = MonthView.prototype

      _proto.UNSAFE_componentWillReceiveProps = function UNSAFE_componentWillReceiveProps(
        _ref2
      ) {
        var date = _ref2.date
        this.setState({
          needLimitMeasure: !eq(date, this.props.date, 'month'),
        })
      }

      _proto.componentDidMount = function componentDidMount() {
        var _this2 = this

        var running
        if (this.state.needLimitMeasure) this.measureRowLimit(this.props)
        window.addEventListener(
          'resize',
          (this._resizeListener = function() {
            if (!running) {
              request(function() {
                running = false

                _this2.setState({
                  needLimitMeasure: true,
                }) //eslint-disable-line
              })
            }
          }),
          false
        )
      }

      _proto.componentDidUpdate = function componentDidUpdate() {
        if (this.state.needLimitMeasure) this.measureRowLimit(this.props)
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        window.removeEventListener('resize', this._resizeListener, false)
      }

      _proto.render = function render() {
        var _this$props5 = this.props,
          date = _this$props5.date,
          localizer = _this$props5.localizer,
          className = _this$props5.className,
          month = visibleDays(date, localizer),
          weeks = chunk(month, 7)
        this._weekCount = weeks.length
        return React__default.createElement(
          'div',
          {
            className: clsx('rbc-month-view', className),
            role: 'table',
            'aria-label': 'Month View',
          },
          React__default.createElement(
            'div',
            {
              className: 'rbc-row rbc-month-header',
              role: 'row',
            },
            this.renderHeaders(weeks[0])
          ),
          weeks.map(this.renderWeek)
        )
      }

      _proto.renderHeaders = function renderHeaders(row) {
        var _this$props6 = this.props,
          localizer = _this$props6.localizer,
          components = _this$props6.components
        var first = row[0]
        var last = row[row.length - 1]
        var HeaderComponent = components.header || Header
        return range(first, last, 'day').map(function(day, idx) {
          return React__default.createElement(
            'div',
            {
              key: 'header_' + idx,
              className: 'rbc-header',
            },
            React__default.createElement(HeaderComponent, {
              date: day,
              localizer: localizer,
              label: localizer.format(day, 'weekdayFormat'),
            })
          )
        })
      }

      _proto.measureRowLimit = function measureRowLimit() {
        this.setState({
          needLimitMeasure: false,
          rowLimit: this.slotRowRef.current.getRowLimit(),
        })
      }

      _proto.selectDates = function selectDates(slotInfo) {
        var slots = this._pendingSelection.slice()

        this._pendingSelection = []
        slots.sort(function(a, b) {
          return +a - +b
        })
        notify(this.props.onSelectSlot, {
          slots: slots,
          start: slots[0],
          end: slots[slots.length - 1],
          action: slotInfo.action,
          bounds: slotInfo.bounds,
          box: slotInfo.box,
        })
      }

      _proto.clearSelection = function clearSelection() {
        clearTimeout(this._selectTimer)
        this._pendingSelection = []
      }

      return MonthView
    })(React__default.Component)

  MonthView.propTypes = {
    events: propTypes.array.isRequired,
    date: propTypes.instanceOf(Date),
    min: propTypes.instanceOf(Date),
    max: propTypes.instanceOf(Date),
    step: propTypes.number,
    getNow: propTypes.func.isRequired,
    scrollToTime: propTypes.instanceOf(Date),
    rtl: propTypes.bool,
    resizable: propTypes.bool,
    width: propTypes.number,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onNavigate: propTypes.func,
    onSelectSlot: propTypes.func,
    onSelectEvent: propTypes.func,
    onDoubleClickEvent: propTypes.func,
    onKeyPressEvent: propTypes.func,
    onShowMore: propTypes.func,
    showAllEvents: propTypes.bool,
    onDrillDown: propTypes.func,
    getDrilldownView: propTypes.func.isRequired,
    popup: propTypes.bool,
    handleDragStart: propTypes.func,
    popupOffset: propTypes.oneOfType([
      propTypes.number,
      propTypes.shape({
        x: propTypes.number,
        y: propTypes.number,
      }),
    ]),
  }

  MonthView.range = function(date, _ref3) {
    var localizer = _ref3.localizer
    var start = firstVisibleDay(date, localizer)
    var end = lastVisibleDay(date, localizer)
    return {
      start: start,
      end: end,
    }
  }

  MonthView.navigate = function(date, action) {
    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -1, 'month')

      case navigate.NEXT:
        return add(date, 1, 'month')

      default:
        return date
    }
  }

  MonthView.title = function(date, _ref4) {
    var localizer = _ref4.localizer
    return localizer.format(date, 'monthHeaderFormat')
  }

  var getDstOffset = function getDstOffset(start, end) {
    return start.getTimezoneOffset() - end.getTimezoneOffset()
  }

  var getKey$1 = function getKey(min, max, step, slots) {
    return (
      '' +
      +startOf(min, 'minutes') +
      ('' + +startOf(max, 'minutes')) +
      (step + '-' + slots)
    )
  }

  function getSlotMetrics$1(_ref) {
    var start = _ref.min,
      end = _ref.max,
      step = _ref.step,
      timeslots = _ref.timeslots
    var key = getKey$1(start, end, step, timeslots) // if the start is on a DST-changing day but *after* the moment of DST
    // transition we need to add those extra minutes to our minutesFromMidnight

    var daystart = startOf(start, 'day')
    var daystartdstoffset = getDstOffset(daystart, start)
    var totalMin = 1 + diff(start, end, 'minutes') + getDstOffset(start, end)
    var minutesFromMidnight =
      diff(daystart, start, 'minutes') + daystartdstoffset
    var numGroups = Math.ceil(totalMin / (step * timeslots))
    var numSlots = numGroups * timeslots
    var groups = new Array(numGroups)
    var slots = new Array(numSlots) // Each slot date is created from "zero", instead of adding `step` to
    // the previous one, in order to avoid DST oddities

    for (var grp = 0; grp < numGroups; grp++) {
      groups[grp] = new Array(timeslots)

      for (var slot = 0; slot < timeslots; slot++) {
        var slotIdx = grp * timeslots + slot
        var minFromStart = slotIdx * step // A date with total minutes calculated from the start of the day

        slots[slotIdx] = groups[grp][slot] = new Date(
          start.getFullYear(),
          start.getMonth(),
          start.getDate(),
          0,
          minutesFromMidnight + minFromStart,
          0,
          0
        )
      }
    } // Necessary to be able to select up until the last timeslot in a day

    var lastSlotMinFromStart = slots.length * step
    slots.push(
      new Date(
        start.getFullYear(),
        start.getMonth(),
        start.getDate(),
        0,
        minutesFromMidnight + lastSlotMinFromStart,
        0,
        0
      )
    )

    function positionFromDate(date) {
      var diff$1 = diff(start, date, 'minutes') + getDstOffset(start, date)
      return Math.min(diff$1, totalMin)
    }

    return {
      groups: groups,
      update: function update(args) {
        if (getKey$1(args) !== key) return getSlotMetrics$1(args)
        return this
      },
      dateIsInGroup: function dateIsInGroup(date, groupIndex) {
        var nextGroup = groups[groupIndex + 1]
        return inRange(
          date,
          groups[groupIndex][0],
          nextGroup ? nextGroup[0] : end,
          'minutes'
        )
      },
      nextSlot: function nextSlot(slot) {
        var next = slots[Math.min(slots.indexOf(slot) + 1, slots.length - 1)] // in the case of the last slot we won't a long enough range so manually get it

        if (next === slot) next = add(slot, step, 'minutes')
        return next
      },
      closestSlotToPosition: function closestSlotToPosition(percent) {
        var slot = Math.min(
          slots.length - 1,
          Math.max(0, Math.floor(percent * numSlots))
        )
        return slots[slot]
      },
      closestSlotFromPoint: function closestSlotFromPoint(point, boundaryRect) {
        var range = Math.abs(boundaryRect.top - boundaryRect.bottom)
        return this.closestSlotToPosition((point.y - boundaryRect.top) / range)
      },
      closestSlotFromDate: function closestSlotFromDate(date, offset) {
        if (offset === void 0) {
          offset = 0
        }

        if (lt(date, start, 'minutes')) return slots[0]
        var diffMins = diff(start, date, 'minutes')
        return slots[(diffMins - (diffMins % step)) / step + offset]
      },
      startsBeforeDay: function startsBeforeDay(date) {
        return lt(date, start, 'day')
      },
      startsAfterDay: function startsAfterDay(date) {
        return gt(date, end, 'day')
      },
      startsBefore: function startsBefore(date) {
        return lt(merge(start, date), start, 'minutes')
      },
      startsAfter: function startsAfter(date) {
        return gt(merge(end, date), end, 'minutes')
      },
      getRange: function getRange(rangeStart, rangeEnd, ignoreMin, ignoreMax) {
        if (!ignoreMin) rangeStart = min(end, max(start, rangeStart))
        if (!ignoreMax) rangeEnd = min(end, max(start, rangeEnd))
        var rangeStartMin = positionFromDate(rangeStart)
        var rangeEndMin = positionFromDate(rangeEnd)
        var top =
          rangeEndMin > step * numSlots && !eq(end, rangeEnd)
            ? ((rangeStartMin - step) / (step * numSlots)) * 100
            : (rangeStartMin / (step * numSlots)) * 100
        return {
          top: top,
          height: (rangeEndMin / (step * numSlots)) * 100 - top,
          start: positionFromDate(rangeStart),
          startDate: rangeStart,
          end: positionFromDate(rangeEnd),
          endDate: rangeEnd,
        }
      },
      getCurrentTimePosition: function getCurrentTimePosition(rangeStart) {
        var rangeStartMin = positionFromDate(rangeStart)
        var top = (rangeStartMin / (step * numSlots)) * 100
        return top
      },
    }
  }

  function _defineProperties(target, props) {
    for (var i = 0; i < props.length; i++) {
      var descriptor = props[i]
      descriptor.enumerable = descriptor.enumerable || false
      descriptor.configurable = true
      if ('value' in descriptor) descriptor.writable = true
      Object.defineProperty(target, descriptor.key, descriptor)
    }
  }

  function _createClass(Constructor, protoProps, staticProps) {
    if (protoProps) _defineProperties(Constructor.prototype, protoProps)
    if (staticProps) _defineProperties(Constructor, staticProps)
    return Constructor
  }

  /** Built-in value references. */
  var spreadableSymbol = Symbol$1 ? Symbol$1.isConcatSpreadable : undefined

  /**
   * Checks if `value` is a flattenable `arguments` object or array.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is flattenable, else `false`.
   */
  function isFlattenable(value) {
    return (
      isArray(value) ||
      isArguments(value) ||
      !!(spreadableSymbol && value && value[spreadableSymbol])
    )
  }

  /**
   * The base implementation of `_.flatten` with support for restricting flattening.
   *
   * @private
   * @param {Array} array The array to flatten.
   * @param {number} depth The maximum recursion depth.
   * @param {boolean} [predicate=isFlattenable] The function invoked per iteration.
   * @param {boolean} [isStrict] Restrict to values that pass `predicate` checks.
   * @param {Array} [result=[]] The initial result value.
   * @returns {Array} Returns the new flattened array.
   */
  function baseFlatten(array, depth, predicate, isStrict, result) {
    var index = -1,
      length = array.length

    predicate || (predicate = isFlattenable)
    result || (result = [])

    while (++index < length) {
      var value = array[index]
      if (depth > 0 && predicate(value)) {
        if (depth > 1) {
          // Recursively flatten arrays (susceptible to call stack limits).
          baseFlatten(value, depth - 1, predicate, isStrict, result)
        } else {
          arrayPush(result, value)
        }
      } else if (!isStrict) {
        result[result.length] = value
      }
    }
    return result
  }

  /**
   * Creates a base function for methods like `_.forIn` and `_.forOwn`.
   *
   * @private
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Function} Returns the new base function.
   */
  function createBaseFor(fromRight) {
    return function(object, iteratee, keysFunc) {
      var index = -1,
        iterable = Object(object),
        props = keysFunc(object),
        length = props.length

      while (length--) {
        var key = props[fromRight ? length : ++index]
        if (iteratee(iterable[key], key, iterable) === false) {
          break
        }
      }
      return object
    }
  }

  /**
   * The base implementation of `baseForOwn` which iterates over `object`
   * properties returned by `keysFunc` and invokes `iteratee` for each property.
   * Iteratee functions may exit iteration early by explicitly returning `false`.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {Function} keysFunc The function to get the keys of `object`.
   * @returns {Object} Returns `object`.
   */
  var baseFor = createBaseFor()

  /**
   * The base implementation of `_.forOwn` without support for iteratee shorthands.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Object} Returns `object`.
   */
  function baseForOwn(object, iteratee) {
    return object && baseFor(object, iteratee, keys)
  }

  /**
   * Creates a `baseEach` or `baseEachRight` function.
   *
   * @private
   * @param {Function} eachFunc The function to iterate over a collection.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Function} Returns the new base function.
   */
  function createBaseEach(eachFunc, fromRight) {
    return function(collection, iteratee) {
      if (collection == null) {
        return collection
      }
      if (!isArrayLike(collection)) {
        return eachFunc(collection, iteratee)
      }
      var length = collection.length,
        index = fromRight ? length : -1,
        iterable = Object(collection)

      while (fromRight ? index-- : ++index < length) {
        if (iteratee(iterable[index], index, iterable) === false) {
          break
        }
      }
      return collection
    }
  }

  /**
   * The base implementation of `_.forEach` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array|Object} Returns `collection`.
   */
  var baseEach = createBaseEach(baseForOwn)

  /**
   * The base implementation of `_.map` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the new mapped array.
   */
  function baseMap(collection, iteratee) {
    var index = -1,
      result = isArrayLike(collection) ? Array(collection.length) : []

    baseEach(collection, function(value, key, collection) {
      result[++index] = iteratee(value, key, collection)
    })
    return result
  }

  /**
   * The base implementation of `_.sortBy` which uses `comparer` to define the
   * sort order of `array` and replaces criteria objects with their corresponding
   * values.
   *
   * @private
   * @param {Array} array The array to sort.
   * @param {Function} comparer The function to define sort order.
   * @returns {Array} Returns `array`.
   */
  function baseSortBy(array, comparer) {
    var length = array.length

    array.sort(comparer)
    while (length--) {
      array[length] = array[length].value
    }
    return array
  }

  /**
   * Compares values to sort them in ascending order.
   *
   * @private
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {number} Returns the sort order indicator for `value`.
   */
  function compareAscending(value, other) {
    if (value !== other) {
      var valIsDefined = value !== undefined,
        valIsNull = value === null,
        valIsReflexive = value === value,
        valIsSymbol = isSymbol(value)

      var othIsDefined = other !== undefined,
        othIsNull = other === null,
        othIsReflexive = other === other,
        othIsSymbol = isSymbol(other)

      if (
        (!othIsNull && !othIsSymbol && !valIsSymbol && value > other) ||
        (valIsSymbol &&
          othIsDefined &&
          othIsReflexive &&
          !othIsNull &&
          !othIsSymbol) ||
        (valIsNull && othIsDefined && othIsReflexive) ||
        (!valIsDefined && othIsReflexive) ||
        !valIsReflexive
      ) {
        return 1
      }
      if (
        (!valIsNull && !valIsSymbol && !othIsSymbol && value < other) ||
        (othIsSymbol &&
          valIsDefined &&
          valIsReflexive &&
          !valIsNull &&
          !valIsSymbol) ||
        (othIsNull && valIsDefined && valIsReflexive) ||
        (!othIsDefined && valIsReflexive) ||
        !othIsReflexive
      ) {
        return -1
      }
    }
    return 0
  }

  /**
   * Used by `_.orderBy` to compare multiple properties of a value to another
   * and stable sort them.
   *
   * If `orders` is unspecified, all values are sorted in ascending order. Otherwise,
   * specify an order of "desc" for descending or "asc" for ascending sort order
   * of corresponding values.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {boolean[]|string[]} orders The order to sort by for each property.
   * @returns {number} Returns the sort order indicator for `object`.
   */
  function compareMultiple(object, other, orders) {
    var index = -1,
      objCriteria = object.criteria,
      othCriteria = other.criteria,
      length = objCriteria.length,
      ordersLength = orders.length

    while (++index < length) {
      var result = compareAscending(objCriteria[index], othCriteria[index])
      if (result) {
        if (index >= ordersLength) {
          return result
        }
        var order = orders[index]
        return result * (order == 'desc' ? -1 : 1)
      }
    }
    // Fixes an `Array#sort` bug in the JS engine embedded in Adobe applications
    // that causes it, under certain circumstances, to provide the same value for
    // `object` and `other`. See https://github.com/jashkenas/underscore/pull/1247
    // for more details.
    //
    // This also ensures a stable sort in V8 and other engines.
    // See https://bugs.chromium.org/p/v8/issues/detail?id=90 for more details.
    return object.index - other.index
  }

  /**
   * The base implementation of `_.orderBy` without param guards.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function[]|Object[]|string[]} iteratees The iteratees to sort by.
   * @param {string[]} orders The sort orders of `iteratees`.
   * @returns {Array} Returns the new sorted array.
   */
  function baseOrderBy(collection, iteratees, orders) {
    var index = -1
    iteratees = arrayMap(
      iteratees.length ? iteratees : [identity],
      baseUnary(baseIteratee)
    )

    var result = baseMap(collection, function(value, key, collection) {
      var criteria = arrayMap(iteratees, function(iteratee) {
        return iteratee(value)
      })
      return { criteria: criteria, index: ++index, value: value }
    })

    return baseSortBy(result, function(object, other) {
      return compareMultiple(object, other, orders)
    })
  }

  /**
   * A faster alternative to `Function#apply`, this function invokes `func`
   * with the `this` binding of `thisArg` and the arguments of `args`.
   *
   * @private
   * @param {Function} func The function to invoke.
   * @param {*} thisArg The `this` binding of `func`.
   * @param {Array} args The arguments to invoke `func` with.
   * @returns {*} Returns the result of `func`.
   */
  function apply(func, thisArg, args) {
    switch (args.length) {
      case 0:
        return func.call(thisArg)
      case 1:
        return func.call(thisArg, args[0])
      case 2:
        return func.call(thisArg, args[0], args[1])
      case 3:
        return func.call(thisArg, args[0], args[1], args[2])
    }
    return func.apply(thisArg, args)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$4 = Math.max

  /**
   * A specialized version of `baseRest` which transforms the rest array.
   *
   * @private
   * @param {Function} func The function to apply a rest parameter to.
   * @param {number} [start=func.length-1] The start position of the rest parameter.
   * @param {Function} transform The rest array transform.
   * @returns {Function} Returns the new function.
   */
  function overRest(func, start, transform) {
    start = nativeMax$4(start === undefined ? func.length - 1 : start, 0)
    return function() {
      var args = arguments,
        index = -1,
        length = nativeMax$4(args.length - start, 0),
        array = Array(length)

      while (++index < length) {
        array[index] = args[start + index]
      }
      index = -1
      var otherArgs = Array(start + 1)
      while (++index < start) {
        otherArgs[index] = args[index]
      }
      otherArgs[start] = transform(array)
      return apply(func, this, otherArgs)
    }
  }

  /**
   * Creates a function that returns `value`.
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Util
   * @param {*} value The value to return from the new function.
   * @returns {Function} Returns the new constant function.
   * @example
   *
   * var objects = _.times(2, _.constant({ 'a': 1 }));
   *
   * console.log(objects);
   * // => [{ 'a': 1 }, { 'a': 1 }]
   *
   * console.log(objects[0] === objects[1]);
   * // => true
   */
  function constant(value) {
    return function() {
      return value
    }
  }

  var defineProperty = (function() {
    try {
      var func = getNative$1(Object, 'defineProperty')
      func({}, '', {})
      return func
    } catch (e) {}
  })()

  /**
   * The base implementation of `setToString` without support for hot loop shorting.
   *
   * @private
   * @param {Function} func The function to modify.
   * @param {Function} string The `toString` result.
   * @returns {Function} Returns `func`.
   */
  var baseSetToString = !defineProperty
    ? identity
    : function(func, string) {
        return defineProperty(func, 'toString', {
          configurable: true,
          enumerable: false,
          value: constant(string),
          writable: true,
        })
      }

  /** Used to detect hot functions by number of calls within a span of milliseconds. */
  var HOT_COUNT = 800,
    HOT_SPAN = 16

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeNow$1 = Date.now

  /**
   * Creates a function that'll short out and invoke `identity` instead
   * of `func` when it's called `HOT_COUNT` or more times in `HOT_SPAN`
   * milliseconds.
   *
   * @private
   * @param {Function} func The function to restrict.
   * @returns {Function} Returns the new shortable function.
   */
  function shortOut(func) {
    var count = 0,
      lastCalled = 0

    return function() {
      var stamp = nativeNow$1(),
        remaining = HOT_SPAN - (stamp - lastCalled)

      lastCalled = stamp
      if (remaining > 0) {
        if (++count >= HOT_COUNT) {
          return arguments[0]
        }
      } else {
        count = 0
      }
      return func.apply(undefined, arguments)
    }
  }

  /**
   * Sets the `toString` method of `func` to return `string`.
   *
   * @private
   * @param {Function} func The function to modify.
   * @param {Function} string The `toString` result.
   * @returns {Function} Returns `func`.
   */
  var setToString = shortOut(baseSetToString)

  /**
   * The base implementation of `_.rest` which doesn't validate or coerce arguments.
   *
   * @private
   * @param {Function} func The function to apply a rest parameter to.
   * @param {number} [start=func.length-1] The start position of the rest parameter.
   * @returns {Function} Returns the new function.
   */
  function baseRest(func, start) {
    return setToString(overRest(func, start, identity), func + '')
  }

  /**
   * Creates an array of elements, sorted in ascending order by the results of
   * running each element in a collection thru each iteratee. This method
   * performs a stable sort, that is, it preserves the original sort order of
   * equal elements. The iteratees are invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {...(Function|Function[])} [iteratees=[_.identity]]
   *  The iteratees to sort by.
   * @returns {Array} Returns the new sorted array.
   * @example
   *
   * var users = [
   *   { 'user': 'fred',   'age': 48 },
   *   { 'user': 'barney', 'age': 36 },
   *   { 'user': 'fred',   'age': 40 },
   *   { 'user': 'barney', 'age': 34 }
   * ];
   *
   * _.sortBy(users, [function(o) { return o.user; }]);
   * // => objects for [['barney', 36], ['barney', 34], ['fred', 48], ['fred', 40]]
   *
   * _.sortBy(users, ['user', 'age']);
   * // => objects for [['barney', 34], ['barney', 36], ['fred', 40], ['fred', 48]]
   */
  var sortBy = baseRest(function(collection, iteratees) {
    if (collection == null) {
      return []
    }
    var length = iteratees.length
    if (length > 1 && isIterateeCall(collection, iteratees[0], iteratees[1])) {
      iteratees = []
    } else if (
      length > 2 &&
      isIterateeCall(iteratees[0], iteratees[1], iteratees[2])
    ) {
      iteratees = [iteratees[0]]
    }
    return baseOrderBy(collection, baseFlatten(iteratees, 1), [])
  })

  var Event =
    /*#__PURE__*/
    (function() {
      function Event(data, _ref) {
        var accessors = _ref.accessors,
          slotMetrics = _ref.slotMetrics

        var _slotMetrics$getRange = slotMetrics.getRange(
            accessors.start(data),
            accessors.end(data)
          ),
          start = _slotMetrics$getRange.start,
          startDate = _slotMetrics$getRange.startDate,
          end = _slotMetrics$getRange.end,
          endDate = _slotMetrics$getRange.endDate,
          top = _slotMetrics$getRange.top,
          height = _slotMetrics$getRange.height

        this.start = start
        this.end = end
        this.startMs = +startDate
        this.endMs = +endDate
        this.top = top
        this.height = height
        this.data = data
      }
      /**
       * The event's width without any overlap.
       */

      _createClass(Event, [
        {
          key: '_width',
          get: function get() {
            // The container event's width is determined by the maximum number of
            // events in any of its rows.
            if (this.rows) {
              var columns =
                this.rows.reduce(
                  function(max, row) {
                    return Math.max(max, row.leaves.length + 1)
                  }, // add itself
                  0
                ) + 1 // add the container

              return 100 / columns
            }

            var availableWidth = 100 - this.container._width // The row event's width is the space left by the container, divided
            // among itself and its leaves.

            if (this.leaves) {
              return availableWidth / (this.leaves.length + 1)
            } // The leaf event's width is determined by its row's width

            return this.row._width
          },
          /**
           * The event's calculated width, possibly with extra width added for
           * overlapping effect.
           */
        },
        {
          key: 'width',
          get: function get() {
            var noOverlap = this._width
            var overlap = Math.min(100, this._width * 1.7) // Containers can always grow.

            if (this.rows) {
              return overlap
            } // Rows can grow if they have leaves.

            if (this.leaves) {
              return this.leaves.length > 0 ? overlap : noOverlap
            } // Leaves can grow unless they're the last item in a row.

            var leaves = this.row.leaves
            var index = leaves.indexOf(this)
            return index === leaves.length - 1 ? noOverlap : overlap
          },
        },
        {
          key: 'xOffset',
          get: function get() {
            // Containers have no offset.
            if (this.rows) return 0 // Rows always start where their container ends.

            if (this.leaves) return this.container._width // Leaves are spread out evenly on the space left by its row.

            var _this$row = this.row,
              leaves = _this$row.leaves,
              xOffset = _this$row.xOffset,
              _width = _this$row._width
            var index = leaves.indexOf(this) + 1
            return xOffset + index * _width
          },
        },
      ])

      return Event
    })()
  /**
   * Return true if event a and b is considered to be on the same row.
   */

  function onSameRow(a, b, minimumStartDifference) {
    return (
      // Occupies the same start slot.
      Math.abs(b.start - a.start) < minimumStartDifference || // A's start slot overlaps with b's end slot.
      (b.start > a.start && b.start < a.end)
    )
  }

  function sortByRender(events) {
    var sortedByTime = sortBy(events, [
      'startMs',
      function(e) {
        return -e.endMs
      },
    ])
    var sorted = []

    while (sortedByTime.length > 0) {
      var event = sortedByTime.shift()
      sorted.push(event)

      for (var i = 0; i < sortedByTime.length; i++) {
        var test = sortedByTime[i] // Still inside this event, look for next.

        if (event.endMs > test.startMs) continue // We've found the first event of the next event group.
        // If that event is not right next to our current event, we have to
        // move it here.

        if (i > 0) {
          var _event = sortedByTime.splice(i, 1)[0]
          sorted.push(_event)
        } // We've already found the next event group, so stop looking.

        break
      }
    }

    return sorted
  }

  function getStyledEvents(_ref2) {
    var events = _ref2.events,
      minimumStartDifference = _ref2.minimumStartDifference,
      slotMetrics = _ref2.slotMetrics,
      accessors = _ref2.accessors
    // Create proxy events and order them so that we don't have
    // to fiddle with z-indexes.
    var proxies = events.map(function(event) {
      return new Event(event, {
        slotMetrics: slotMetrics,
        accessors: accessors,
      })
    })
    var eventsInRenderOrder = sortByRender(proxies) // Group overlapping events, while keeping order.
    // Every event is always one of: container, row or leaf.
    // Containers can contain rows, and rows can contain leaves.

    var containerEvents = []

    var _loop = function _loop(i) {
      var event = eventsInRenderOrder[i] // Check if this event can go into a container event.

      var container = containerEvents.find(function(c) {
        return (
          c.end > event.start ||
          Math.abs(event.start - c.start) < minimumStartDifference
        )
      }) // Couldn't find a container — that means this event is a container.

      if (!container) {
        event.rows = []
        containerEvents.push(event)
        return 'continue'
      } // Found a container for the event.

      event.container = container // Check if the event can be placed in an existing row.
      // Start looking from behind.

      var row = null

      for (var j = container.rows.length - 1; !row && j >= 0; j--) {
        if (onSameRow(container.rows[j], event, minimumStartDifference)) {
          row = container.rows[j]
        }
      }

      if (row) {
        // Found a row, so add it.
        row.leaves.push(event)
        event.row = row
      } else {
        // Couldn't find a row – that means this event is a row.
        event.leaves = []
        container.rows.push(event)
      }
    }

    for (var i = 0; i < eventsInRenderOrder.length; i++) {
      var _ret = _loop(i)

      if (_ret === 'continue') continue
    } // Return the original events, along with their styles.

    return eventsInRenderOrder.map(function(event) {
      return {
        event: event.data,
        style: {
          top: event.top,
          height: event.height,
          width: event.width,
          xOffset: Math.max(0, event.xOffset),
        },
      }
    })
  }

  function getMaxIdxDFS(node, maxIdx, visited) {
    for (var i = 0; i < node.friends.length; ++i) {
      if (visited.indexOf(node.friends[i]) > -1) continue
      maxIdx = maxIdx > node.friends[i].idx ? maxIdx : node.friends[i].idx // TODO : trace it by not object but kinda index or something for performance

      visited.push(node.friends[i])
      var newIdx = getMaxIdxDFS(node.friends[i], maxIdx, visited)
      maxIdx = maxIdx > newIdx ? maxIdx : newIdx
    }

    return maxIdx
  }

  function noOverlap(_ref) {
    var events = _ref.events,
      minimumStartDifference = _ref.minimumStartDifference,
      slotMetrics = _ref.slotMetrics,
      accessors = _ref.accessors
    var styledEvents = getStyledEvents({
      events: events,
      minimumStartDifference: minimumStartDifference,
      slotMetrics: slotMetrics,
      accessors: accessors,
    })
    styledEvents.sort(function(a, b) {
      a = a.style
      b = b.style
      if (a.top !== b.top) return a.top > b.top ? 1 : -1
      else return a.top + a.height < b.top + b.height ? 1 : -1
    })

    for (var i = 0; i < styledEvents.length; ++i) {
      styledEvents[i].friends = []
      delete styledEvents[i].style.left
      delete styledEvents[i].style.left
      delete styledEvents[i].idx
      delete styledEvents[i].size
    }

    for (var _i = 0; _i < styledEvents.length - 1; ++_i) {
      var se1 = styledEvents[_i]
      var y1 = se1.style.top
      var y2 = se1.style.top + se1.style.height

      for (var j = _i + 1; j < styledEvents.length; ++j) {
        var se2 = styledEvents[j]
        var y3 = se2.style.top
        var y4 = se2.style.top + se2.style.height // be friends when overlapped

        if ((y3 <= y1 && y1 < y4) || (y1 <= y3 && y3 < y2)) {
          // TODO : hashmap would be effective for performance
          se1.friends.push(se2)
          se2.friends.push(se1)
        }
      }
    }

    for (var _i2 = 0; _i2 < styledEvents.length; ++_i2) {
      var se = styledEvents[_i2]
      var bitmap = []

      for (var _j = 0; _j < 100; ++_j) {
        bitmap.push(1)
      } // 1 means available

      for (var _j2 = 0; _j2 < se.friends.length; ++_j2) {
        if (se.friends[_j2].idx !== undefined) bitmap[se.friends[_j2].idx] = 0
      } // 0 means reserved

      se.idx = bitmap.indexOf(1)
    }

    for (var _i3 = 0; _i3 < styledEvents.length; ++_i3) {
      var size = 0
      if (styledEvents[_i3].size) continue
      var allFriends = []
      var maxIdx = getMaxIdxDFS(styledEvents[_i3], 0, allFriends)
      size = 100 / (maxIdx + 1)
      styledEvents[_i3].size = size

      for (var _j3 = 0; _j3 < allFriends.length; ++_j3) {
        allFriends[_j3].size = size
      }
    }

    for (var _i4 = 0; _i4 < styledEvents.length; ++_i4) {
      var e = styledEvents[_i4]
      e.style.left = e.idx * e.size // stretch to maximum

      var _maxIdx = 0

      for (var _j4 = 0; _j4 < e.friends.length; ++_j4) {
        var idx = e.friends[_j4]
        _maxIdx = _maxIdx > idx ? _maxIdx : idx
      }

      if (_maxIdx <= e.idx) e.size = 100 - e.idx * e.size // padding between events
      // for this feature, `width` is not percentage based unit anymore
      // it will be used with calc()

      var padding = e.idx === 0 ? 0 : 3
      e.style.width = 'calc(' + e.size + '% - ' + padding + 'px)'
      e.style.height = 'calc(' + e.style.height + '% - 2px)'
      e.style.xOffset = 'calc(' + e.style.left + '% + ' + padding + 'px)'
    }

    return styledEvents
  }

  /*eslint no-unused-vars: "off"*/
  var DefaultAlgorithms = {
    overlap: getStyledEvents,
    'no-overlap': noOverlap,
  }

  function isFunction$2(a) {
    return !!(a && a.constructor && a.call && a.apply)
  } //

  function getStyledEvents$1(_ref) {
    var events = _ref.events,
      minimumStartDifference = _ref.minimumStartDifference,
      slotMetrics = _ref.slotMetrics,
      accessors = _ref.accessors,
      dayLayoutAlgorithm = _ref.dayLayoutAlgorithm
    var algorithm = dayLayoutAlgorithm
    if (dayLayoutAlgorithm in DefaultAlgorithms)
      algorithm = DefaultAlgorithms[dayLayoutAlgorithm]

    if (!isFunction$2(algorithm)) {
      // invalid algorithm
      return []
    }

    return algorithm.apply(this, arguments)
  }

  var TimeSlotGroup =
    /*#__PURE__*/
    (function(_Component) {
      _inheritsLoose(TimeSlotGroup, _Component)

      function TimeSlotGroup() {
        return _Component.apply(this, arguments) || this
      }

      var _proto = TimeSlotGroup.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          renderSlot = _this$props.renderSlot,
          resource = _this$props.resource,
          group = _this$props.group,
          getters = _this$props.getters,
          _this$props$component = _this$props.components
        _this$props$component =
          _this$props$component === void 0 ? {} : _this$props$component
        var _this$props$component2 = _this$props$component.timeSlotWrapper,
          Wrapper =
            _this$props$component2 === void 0
              ? NoopWrapper
              : _this$props$component2
        var groupProps = getters ? getters.slotGroupProp() : {}
        return React__default.createElement(
          'div',
          _extends(
            {
              className: 'rbc-timeslot-group',
            },
            groupProps
          ),
          group.map(function(value, idx) {
            var slotProps = getters ? getters.slotProp(value, resource) : {}
            return React__default.createElement(
              Wrapper,
              {
                key: idx,
                value: value,
                resource: resource,
              },
              React__default.createElement(
                'div',
                _extends({}, slotProps, {
                  className: clsx('rbc-time-slot', slotProps.className),
                }),
                renderSlot && renderSlot(value, idx)
              )
            )
          })
        )
      }

      return TimeSlotGroup
    })(React.Component)
  TimeSlotGroup.propTypes = {
    renderSlot: propTypes.func,
    group: propTypes.array.isRequired,
    resource: propTypes.any,
    components: propTypes.object,
    getters: propTypes.object,
  }

  function stringifyPercent(v) {
    return typeof v === 'string' ? v : v + '%'
  }
  /* eslint-disable react/prop-types */

  function TimeGridEvent(props) {
    var _extends2, _extends3

    var style = props.style,
      className = props.className,
      event = props.event,
      accessors = props.accessors,
      rtl = props.rtl,
      selected = props.selected,
      label = props.label,
      continuesEarlier = props.continuesEarlier,
      continuesLater = props.continuesLater,
      getters = props.getters,
      onClick = props.onClick,
      onDoubleClick = props.onDoubleClick,
      isBackgroundEvent = props.isBackgroundEvent,
      onKeyPress = props.onKeyPress,
      _props$components = props.components,
      Event = _props$components.event,
      EventWrapper = _props$components.eventWrapper
    var title = accessors.title(event)
    var tooltip = accessors.tooltip(event)
    var end = accessors.end(event)
    var start = accessors.start(event)
    var userProps = getters.eventProp(event, start, end, selected)
    var height = style.height,
      top = style.top,
      width = style.width,
      xOffset = style.xOffset
    var inner = [
      React__default.createElement(
        'div',
        {
          key: '1',
          className: 'rbc-event-label',
        },
        label
      ),
      React__default.createElement(
        'div',
        {
          key: '2',
          className: 'rbc-event-content',
        },
        Event
          ? React__default.createElement(Event, {
              event: event,
              title: title,
            })
          : title
      ),
    ]
    var eventStyle = isBackgroundEvent
      ? _extends(
          {},
          userProps.style,
          ((_extends2 = {
            top: stringifyPercent(top),
            height: stringifyPercent(height),
            // Adding 10px to take events container right margin into account
            width: 'calc(' + width + ' + 10px)',
          }),
          (_extends2[rtl ? 'right' : 'left'] = stringifyPercent(
            Math.max(0, xOffset)
          )),
          _extends2)
        )
      : _extends(
          {},
          userProps.style,
          ((_extends3 = {
            top: stringifyPercent(top),
            width: stringifyPercent(width),
            height: stringifyPercent(height),
          }),
          (_extends3[rtl ? 'right' : 'left'] = stringifyPercent(xOffset)),
          _extends3)
        )
    return React__default.createElement(
      EventWrapper,
      _extends(
        {
          type: 'time',
        },
        props
      ),
      React__default.createElement(
        'div',
        {
          onClick: onClick,
          onDoubleClick: onDoubleClick,
          style: eventStyle,
          onKeyPress: onKeyPress,
          title: tooltip
            ? (typeof label === 'string' ? label + ': ' : '') + tooltip
            : undefined,
          className: clsx(
            isBackgroundEvent ? 'rbc-background-event' : 'rbc-event',
            className,
            userProps.className,
            {
              'rbc-selected': selected,
              'rbc-event-continues-earlier': continuesEarlier,
              'rbc-event-continues-later': continuesLater,
            }
          ),
        },
        inner
      )
    )
  }

  var DayColumn =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(DayColumn, _React$Component)

      function DayColumn() {
        var _this

        for (
          var _len = arguments.length, _args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          _args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(_args)) ||
          this
        _this.state = {
          selecting: false,
          timeIndicatorPosition: null,
        }
        _this.intervalTriggered = false

        _this.renderEvents = function(_ref) {
          var events = _ref.events,
            isBackgroundEvent = _ref.isBackgroundEvent
          var _this$props = _this.props,
            rtl = _this$props.rtl,
            selected = _this$props.selected,
            accessors = _this$props.accessors,
            localizer = _this$props.localizer,
            getters = _this$props.getters,
            components = _this$props.components,
            step = _this$props.step,
            timeslots = _this$props.timeslots,
            dayLayoutAlgorithm = _this$props.dayLayoutAlgorithm,
            resizable = _this$props.resizable

          var _assertThisInitialize = _assertThisInitialized(_this),
            slotMetrics = _assertThisInitialize.slotMetrics

          var messages = localizer.messages
          var styledEvents = getStyledEvents$1({
            events: events,
            accessors: accessors,
            slotMetrics: slotMetrics,
            minimumStartDifference: Math.ceil((step * timeslots) / 2),
            dayLayoutAlgorithm: dayLayoutAlgorithm,
          })
          return styledEvents.map(function(_ref2, idx) {
            var event = _ref2.event,
              style = _ref2.style
            var end = accessors.end(event)
            var start = accessors.start(event)
            var format = 'eventTimeRangeFormat'
            var label
            var startsBeforeDay = slotMetrics.startsBeforeDay(start)
            var startsAfterDay = slotMetrics.startsAfterDay(end)
            if (startsBeforeDay) format = 'eventTimeRangeEndFormat'
            else if (startsAfterDay) format = 'eventTimeRangeStartFormat'
            if (startsBeforeDay && startsAfterDay) label = messages.allDay
            else
              label = localizer.format(
                {
                  start: start,
                  end: end,
                },
                format
              )
            var continuesEarlier =
              startsBeforeDay || slotMetrics.startsBefore(start)
            var continuesLater = startsAfterDay || slotMetrics.startsAfter(end)
            return React__default.createElement(TimeGridEvent, {
              style: style,
              event: event,
              label: label,
              key: 'evt_' + idx,
              getters: getters,
              rtl: rtl,
              components: components,
              continuesEarlier: continuesEarlier,
              continuesLater: continuesLater,
              accessors: accessors,
              selected: isSelected(event, selected),
              onClick: function onClick(e) {
                return _this._select(event, e)
              },
              onDoubleClick: function onDoubleClick(e) {
                return _this._doubleClick(event, e)
              },
              isBackgroundEvent: isBackgroundEvent,
              onKeyPress: function onKeyPress(e) {
                return _this._keyPress(event, e)
              },
              resizable: resizable,
            })
          })
        }

        _this._selectable = function() {
          var node = reactDom.findDOMNode(_assertThisInitialized(_this))
          var selector = (_this._selector = new Selection(
            function() {
              return reactDom.findDOMNode(_assertThisInitialized(_this))
            },
            {
              longPressThreshold: _this.props.longPressThreshold,
            }
          ))

          var maybeSelect = function maybeSelect(box) {
            var onSelecting = _this.props.onSelecting
            var current = _this.state || {}
            var state = selectionState(box)
            var start = state.startDate,
              end = state.endDate

            if (onSelecting) {
              if (
                (eq(current.startDate, start, 'minutes') &&
                  eq(current.endDate, end, 'minutes')) ||
                onSelecting({
                  start: start,
                  end: end,
                  resourceId: _this.props.resource,
                }) === false
              )
                return
            }

            if (
              _this.state.start !== state.start ||
              _this.state.end !== state.end ||
              _this.state.selecting !== state.selecting
            ) {
              _this.setState(state)
            }
          }

          var selectionState = function selectionState(point) {
            var currentSlot = _this.slotMetrics.closestSlotFromPoint(
              point,
              getBoundsForNode(node)
            )

            if (!_this.state.selecting) {
              _this._initialSlot = currentSlot
            }

            var initialSlot = _this._initialSlot

            if (lte(initialSlot, currentSlot)) {
              currentSlot = _this.slotMetrics.nextSlot(currentSlot)
            } else if (gt(initialSlot, currentSlot)) {
              initialSlot = _this.slotMetrics.nextSlot(initialSlot)
            }

            var selectRange = _this.slotMetrics.getRange(
              min(initialSlot, currentSlot),
              max(initialSlot, currentSlot)
            )

            return _extends({}, selectRange, {
              selecting: true,
              top: selectRange.top + '%',
              height: selectRange.height + '%',
            })
          }

          var selectorClicksHandler = function selectorClicksHandler(
            box,
            actionType
          ) {
            if (
              !isEvent(reactDom.findDOMNode(_assertThisInitialized(_this)), box)
            ) {
              var _selectionState = selectionState(box),
                startDate = _selectionState.startDate,
                endDate = _selectionState.endDate

              _this._selectSlot({
                startDate: startDate,
                endDate: endDate,
                action: actionType,
                box: box,
              })
            }

            _this.setState({
              selecting: false,
            })
          }

          selector.on('selecting', maybeSelect)
          selector.on('selectStart', maybeSelect)
          selector.on('beforeSelect', function(box) {
            if (_this.props.selectable !== 'ignoreEvents') return
            return !isEvent(
              reactDom.findDOMNode(_assertThisInitialized(_this)),
              box
            )
          })
          selector.on('click', function(box) {
            return selectorClicksHandler(box, 'click')
          })
          selector.on('doubleClick', function(box) {
            return selectorClicksHandler(box, 'doubleClick')
          })
          selector.on('select', function(bounds) {
            if (_this.state.selecting) {
              _this._selectSlot(
                _extends({}, _this.state, {
                  action: 'select',
                  bounds: bounds,
                })
              )

              _this.setState({
                selecting: false,
              })
            }
          })
          selector.on('reset', function() {
            if (_this.state.selecting) {
              _this.setState({
                selecting: false,
              })
            }
          })
        }

        _this._teardownSelectable = function() {
          if (!_this._selector) return

          _this._selector.teardown()

          _this._selector = null
        }

        _this._selectSlot = function(_ref3) {
          var startDate = _ref3.startDate,
            endDate = _ref3.endDate,
            action = _ref3.action,
            bounds = _ref3.bounds,
            box = _ref3.box
          var current = startDate,
            slots = []

          while (lte(current, endDate)) {
            slots.push(current)
            current = new Date(+current + _this.props.step * 60 * 1000) // using Date ensures not to create an endless loop the day DST begins
          }

          notify(_this.props.onSelectSlot, {
            slots: slots,
            start: startDate,
            end: endDate,
            resourceId: _this.props.resource,
            action: action,
            bounds: bounds,
            box: box,
          })
        }

        _this._select = function() {
          for (
            var _len2 = arguments.length, args = new Array(_len2), _key2 = 0;
            _key2 < _len2;
            _key2++
          ) {
            args[_key2] = arguments[_key2]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this._doubleClick = function() {
          for (
            var _len3 = arguments.length, args = new Array(_len3), _key3 = 0;
            _key3 < _len3;
            _key3++
          ) {
            args[_key3] = arguments[_key3]
          }

          notify(_this.props.onDoubleClickEvent, args)
        }

        _this._keyPress = function() {
          for (
            var _len4 = arguments.length, args = new Array(_len4), _key4 = 0;
            _key4 < _len4;
            _key4++
          ) {
            args[_key4] = arguments[_key4]
          }

          notify(_this.props.onKeyPressEvent, args)
        }

        _this.slotMetrics = getSlotMetrics$1(_this.props)
        return _this
      }

      var _proto = DayColumn.prototype

      _proto.componentDidMount = function componentDidMount() {
        this.props.selectable && this._selectable()

        if (this.props.isNow) {
          this.setTimeIndicatorPositionUpdateInterval()
        }
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        this._teardownSelectable()

        this.clearTimeIndicatorInterval()
      }

      _proto.UNSAFE_componentWillReceiveProps = function UNSAFE_componentWillReceiveProps(
        nextProps
      ) {
        if (nextProps.selectable && !this.props.selectable) this._selectable()
        if (!nextProps.selectable && this.props.selectable)
          this._teardownSelectable()
        this.slotMetrics = this.slotMetrics.update(nextProps)
      }

      _proto.componentDidUpdate = function componentDidUpdate(
        prevProps,
        prevState
      ) {
        var getNowChanged = !eq(
          prevProps.getNow(),
          this.props.getNow(),
          'minutes'
        )

        if (prevProps.isNow !== this.props.isNow || getNowChanged) {
          this.clearTimeIndicatorInterval()

          if (this.props.isNow) {
            var tail =
              !getNowChanged &&
              eq(prevProps.date, this.props.date, 'minutes') &&
              prevState.timeIndicatorPosition ===
                this.state.timeIndicatorPosition
            this.setTimeIndicatorPositionUpdateInterval(tail)
          }
        } else if (
          this.props.isNow &&
          (!eq(prevProps.min, this.props.min, 'minutes') ||
            !eq(prevProps.max, this.props.max, 'minutes'))
        ) {
          this.positionTimeIndicator()
        }
      }
      /**
       * @param tail {Boolean} - whether `positionTimeIndicator` call should be
       *   deferred or called upon setting interval (`true` - if deferred);
       */

      _proto.setTimeIndicatorPositionUpdateInterval = function setTimeIndicatorPositionUpdateInterval(
        tail
      ) {
        var _this2 = this

        if (tail === void 0) {
          tail = false
        }

        if (!this.intervalTriggered && !tail) {
          this.positionTimeIndicator()
        }

        this._timeIndicatorTimeout = window.setTimeout(function() {
          _this2.intervalTriggered = true

          _this2.positionTimeIndicator()

          _this2.setTimeIndicatorPositionUpdateInterval()
        }, 60000)
      }

      _proto.clearTimeIndicatorInterval = function clearTimeIndicatorInterval() {
        this.intervalTriggered = false
        window.clearTimeout(this._timeIndicatorTimeout)
      }

      _proto.positionTimeIndicator = function positionTimeIndicator() {
        var _this$props2 = this.props,
          min = _this$props2.min,
          max = _this$props2.max,
          getNow = _this$props2.getNow
        var current = getNow()

        if (current >= min && current <= max) {
          var top = this.slotMetrics.getCurrentTimePosition(current)
          this.intervalTriggered = true
          this.setState({
            timeIndicatorPosition: top,
          })
        } else {
          this.clearTimeIndicatorInterval()
        }
      }

      _proto.render = function render() {
        var _this$props3 = this.props,
          max = _this$props3.max,
          rtl = _this$props3.rtl,
          isNow = _this$props3.isNow,
          resource = _this$props3.resource,
          accessors = _this$props3.accessors,
          localizer = _this$props3.localizer,
          _this$props3$getters = _this$props3.getters,
          dayProp = _this$props3$getters.dayProp,
          getters = _objectWithoutPropertiesLoose(_this$props3$getters, [
            'dayProp',
          ]),
          _this$props3$componen = _this$props3.components,
          EventContainer = _this$props3$componen.eventContainerWrapper,
          components = _objectWithoutPropertiesLoose(_this$props3$componen, [
            'eventContainerWrapper',
          ])

        var slotMetrics = this.slotMetrics
        var _this$state = this.state,
          selecting = _this$state.selecting,
          top = _this$state.top,
          height = _this$state.height,
          startDate = _this$state.startDate,
          endDate = _this$state.endDate
        var selectDates = {
          start: startDate,
          end: endDate,
        }

        var _dayProp = dayProp(max),
          className = _dayProp.className,
          style = _dayProp.style

        return React__default.createElement(
          'div',
          {
            style: style,
            className: clsx(
              className,
              'rbc-day-slot',
              'rbc-time-column',
              isNow && 'rbc-now',
              isNow && 'rbc-today', // WHY
              selecting && 'rbc-slot-selecting'
            ),
          },
          slotMetrics.groups.map(function(grp, idx) {
            return React__default.createElement(TimeSlotGroup, {
              key: idx,
              group: grp,
              resource: resource,
              getters: getters,
              components: components,
            })
          }),
          React__default.createElement(
            EventContainer,
            {
              localizer: localizer,
              resource: resource,
              accessors: accessors,
              getters: getters,
              components: components,
              slotMetrics: slotMetrics,
            },
            React__default.createElement(
              'div',
              {
                className: clsx('rbc-events-container', rtl && 'rtl'),
              },
              this.renderEvents({
                events: this.props.backgroundEvents,
                isBackgroundEvent: true,
              }),
              this.renderEvents({
                events: this.props.events,
              })
            )
          ),
          selecting &&
            React__default.createElement(
              'div',
              {
                className: 'rbc-slot-selection',
                style: {
                  top: top,
                  height: height,
                },
              },
              React__default.createElement(
                'span',
                null,
                localizer.format(selectDates, 'selectRangeFormat')
              )
            ),
          isNow &&
            this.intervalTriggered &&
            React__default.createElement('div', {
              className: 'rbc-current-time-indicator',
              style: {
                top: this.state.timeIndicatorPosition + '%',
              },
            })
        )
      }

      return DayColumn
    })(React__default.Component)

  DayColumn.propTypes = {
    events: propTypes.array.isRequired,
    backgroundEvents: propTypes.array.isRequired,
    step: propTypes.number.isRequired,
    date: propTypes.instanceOf(Date).isRequired,
    min: propTypes.instanceOf(Date).isRequired,
    max: propTypes.instanceOf(Date).isRequired,
    getNow: propTypes.func.isRequired,
    isNow: propTypes.bool,
    rtl: propTypes.bool,
    resizable: propTypes.bool,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    showMultiDayTimes: propTypes.bool,
    culture: propTypes.string,
    timeslots: propTypes.number,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    eventOffset: propTypes.number,
    longPressThreshold: propTypes.number,
    onSelecting: propTypes.func,
    onSelectSlot: propTypes.func.isRequired,
    onSelectEvent: propTypes.func.isRequired,
    onDoubleClickEvent: propTypes.func.isRequired,
    onKeyPressEvent: propTypes.func,
    className: propTypes.string,
    dragThroughEvents: propTypes.bool,
    resource: propTypes.any,
    dayLayoutAlgorithm: DayLayoutAlgorithmPropType,
  }
  DayColumn.defaultProps = {
    dragThroughEvents: true,
    timeslots: 2,
  }

  var TimeGutter =
    /*#__PURE__*/
    (function(_Component) {
      _inheritsLoose(TimeGutter, _Component)

      function TimeGutter() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this = _Component.call.apply(_Component, [this].concat(args)) || this

        _this.renderSlot = function(value, idx) {
          if (idx !== 0) return null
          var _this$props = _this.props,
            localizer = _this$props.localizer,
            getNow = _this$props.getNow

          var isNow = _this.slotMetrics.dateIsInGroup(getNow(), idx)

          return React__default.createElement(
            'span',
            {
              className: clsx('rbc-label', isNow && 'rbc-now'),
            },
            localizer.format(value, 'timeGutterFormat')
          )
        }

        var _this$props2 = _this.props,
          min = _this$props2.min,
          max = _this$props2.max,
          timeslots = _this$props2.timeslots,
          step = _this$props2.step
        _this.slotMetrics = getSlotMetrics$1({
          min: min,
          max: max,
          timeslots: timeslots,
          step: step,
        })
        return _this
      }

      var _proto = TimeGutter.prototype

      _proto.UNSAFE_componentWillReceiveProps = function UNSAFE_componentWillReceiveProps(
        nextProps
      ) {
        var min = nextProps.min,
          max = nextProps.max,
          timeslots = nextProps.timeslots,
          step = nextProps.step
        this.slotMetrics = this.slotMetrics.update({
          min: min,
          max: max,
          timeslots: timeslots,
          step: step,
        })
      }

      _proto.render = function render() {
        var _this2 = this

        var _this$props3 = this.props,
          resource = _this$props3.resource,
          components = _this$props3.components,
          getters = _this$props3.getters
        return React__default.createElement(
          'div',
          {
            className: 'rbc-time-gutter rbc-time-column',
          },
          this.slotMetrics.groups.map(function(grp, idx) {
            return React__default.createElement(TimeSlotGroup, {
              key: idx,
              group: grp,
              resource: resource,
              components: components,
              renderSlot: _this2.renderSlot,
              getters: getters,
            })
          })
        )
      }

      return TimeGutter
    })(React.Component)
  TimeGutter.propTypes = {
    min: propTypes.instanceOf(Date).isRequired,
    max: propTypes.instanceOf(Date).isRequired,
    timeslots: propTypes.number.isRequired,
    step: propTypes.number.isRequired,
    getNow: propTypes.func.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object,
    localizer: propTypes.object.isRequired,
    resource: propTypes.string,
  }

  function getWidth(node, client) {
    var win = isWindow(node)
    return win ? win.innerWidth : client ? node.clientWidth : offset(node).width
  }

  var size
  function scrollbarSize(recalc) {
    if ((!size && size !== 0) || recalc) {
      if (canUseDOM) {
        var scrollDiv = document.createElement('div')
        scrollDiv.style.position = 'absolute'
        scrollDiv.style.top = '-9999px'
        scrollDiv.style.width = '50px'
        scrollDiv.style.height = '50px'
        scrollDiv.style.overflow = 'scroll'
        document.body.appendChild(scrollDiv)
        size = scrollDiv.offsetWidth - scrollDiv.clientWidth
        document.body.removeChild(scrollDiv)
      }
    }

    return size
  }

  var ResourceHeader = function ResourceHeader(_ref) {
    var label = _ref.label
    return React__default.createElement(React__default.Fragment, null, label)
  }

  ResourceHeader.propTypes = {
    label: propTypes.node,
    index: propTypes.number,
    resource: propTypes.object,
  }

  var TimeGridHeader =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(TimeGridHeader, _React$Component)

      function TimeGridHeader() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(args)) ||
          this

        _this.handleHeaderClick = function(date, view, e) {
          e.preventDefault()
          notify(_this.props.onDrillDown, [date, view])
        }

        _this.renderRow = function(resource) {
          var _this$props = _this.props,
            events = _this$props.events,
            rtl = _this$props.rtl,
            selectable = _this$props.selectable,
            getNow = _this$props.getNow,
            range = _this$props.range,
            getters = _this$props.getters,
            localizer = _this$props.localizer,
            accessors = _this$props.accessors,
            components = _this$props.components,
            resizable = _this$props.resizable
          var resourceId = accessors.resourceId(resource)
          var eventsToDisplay = resource
            ? events.filter(function(event) {
                return accessors.resource(event) === resourceId
              })
            : events
          return React__default.createElement(DateContentRow, {
            isAllDay: true,
            rtl: rtl,
            getNow: getNow,
            minRows: 2,
            range: range,
            events: eventsToDisplay,
            resourceId: resourceId,
            className: 'rbc-allday-cell',
            selectable: selectable,
            selected: _this.props.selected,
            components: components,
            accessors: accessors,
            getters: getters,
            localizer: localizer,
            onSelect: _this.props.onSelectEvent,
            onDoubleClick: _this.props.onDoubleClickEvent,
            onKeyPress: _this.props.onKeyPressEvent,
            onSelectSlot: _this.props.onSelectSlot,
            longPressThreshold: _this.props.longPressThreshold,
            resizable: resizable,
          })
        }

        return _this
      }

      var _proto = TimeGridHeader.prototype

      _proto.renderHeaderCells = function renderHeaderCells(range) {
        var _this2 = this

        var _this$props2 = this.props,
          localizer = _this$props2.localizer,
          getDrilldownView = _this$props2.getDrilldownView,
          getNow = _this$props2.getNow,
          dayProp = _this$props2.getters.dayProp,
          _this$props2$componen = _this$props2.components.header,
          HeaderComponent =
            _this$props2$componen === void 0 ? Header : _this$props2$componen
        var today = getNow()
        return range.map(function(date, i) {
          var drilldownView = getDrilldownView(date)
          var label = localizer.format(date, 'dayFormat')

          var _dayProp = dayProp(date),
            className = _dayProp.className,
            style = _dayProp.style

          var header = React__default.createElement(HeaderComponent, {
            date: date,
            label: label,
            localizer: localizer,
          })
          return React__default.createElement(
            'div',
            {
              key: i,
              style: style,
              className: clsx(
                'rbc-header',
                className,
                eq(date, today, 'day') && 'rbc-today'
              ),
            },
            drilldownView
              ? React__default.createElement(
                  'a',
                  {
                    href: '#',
                    onClick: function onClick(e) {
                      return _this2.handleHeaderClick(date, drilldownView, e)
                    },
                  },
                  header
                )
              : React__default.createElement('span', null, header)
          )
        })
      }

      _proto.render = function render() {
        var _this3 = this

        var _this$props3 = this.props,
          width = _this$props3.width,
          rtl = _this$props3.rtl,
          resources = _this$props3.resources,
          range = _this$props3.range,
          events = _this$props3.events,
          getNow = _this$props3.getNow,
          accessors = _this$props3.accessors,
          selectable = _this$props3.selectable,
          components = _this$props3.components,
          getters = _this$props3.getters,
          scrollRef = _this$props3.scrollRef,
          localizer = _this$props3.localizer,
          isOverflowing = _this$props3.isOverflowing,
          _this$props3$componen = _this$props3.components,
          TimeGutterHeader = _this$props3$componen.timeGutterHeader,
          _this$props3$componen2 = _this$props3$componen.resourceHeader,
          ResourceHeaderComponent =
            _this$props3$componen2 === void 0
              ? ResourceHeader
              : _this$props3$componen2,
          resizable = _this$props3.resizable
        var style = {}

        if (isOverflowing) {
          style[rtl ? 'marginLeft' : 'marginRight'] = scrollbarSize() + 'px'
        }

        var groupedEvents = resources.groupEvents(events)
        return React__default.createElement(
          'div',
          {
            style: style,
            ref: scrollRef,
            className: clsx(
              'rbc-time-header',
              isOverflowing && 'rbc-overflowing'
            ),
          },
          React__default.createElement(
            'div',
            {
              className: 'rbc-label rbc-time-header-gutter',
              style: {
                width: width,
                minWidth: width,
                maxWidth: width,
              },
            },
            TimeGutterHeader &&
              React__default.createElement(TimeGutterHeader, null)
          ),
          resources.map(function(_ref, idx) {
            var id = _ref[0],
              resource = _ref[1]
            return React__default.createElement(
              'div',
              {
                className: 'rbc-time-header-content',
                key: id || idx,
              },
              resource &&
                React__default.createElement(
                  'div',
                  {
                    className: 'rbc-row rbc-row-resource',
                    key: 'resource_' + idx,
                  },
                  React__default.createElement(
                    'div',
                    {
                      className: 'rbc-header',
                    },
                    React__default.createElement(ResourceHeaderComponent, {
                      index: idx,
                      label: accessors.resourceTitle(resource),
                      resource: resource,
                    })
                  )
                ),
              React__default.createElement(
                'div',
                {
                  className:
                    'rbc-row rbc-time-header-cell' +
                    (range.length <= 1
                      ? ' rbc-time-header-cell-single-day'
                      : ''),
                },
                _this3.renderHeaderCells(range)
              ),
              React__default.createElement(DateContentRow, {
                isAllDay: true,
                rtl: rtl,
                getNow: getNow,
                minRows: 2,
                range: range,
                events: groupedEvents.get(id) || [],
                resourceId: resource && id,
                className: 'rbc-allday-cell',
                selectable: selectable,
                selected: _this3.props.selected,
                components: components,
                accessors: accessors,
                getters: getters,
                localizer: localizer,
                onSelect: _this3.props.onSelectEvent,
                onDoubleClick: _this3.props.onDoubleClickEvent,
                onKeyPress: _this3.props.onKeyPressEvent,
                onSelectSlot: _this3.props.onSelectSlot,
                longPressThreshold: _this3.props.longPressThreshold,
                resizable: resizable,
              })
            )
          })
        )
      }

      return TimeGridHeader
    })(React__default.Component)

  TimeGridHeader.propTypes = {
    range: propTypes.array.isRequired,
    events: propTypes.array.isRequired,
    resources: propTypes.object,
    getNow: propTypes.func.isRequired,
    isOverflowing: propTypes.bool,
    rtl: propTypes.bool,
    resizable: propTypes.bool,
    width: propTypes.number,
    localizer: propTypes.object.isRequired,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onSelectSlot: propTypes.func,
    onSelectEvent: propTypes.func,
    onDoubleClickEvent: propTypes.func,
    onKeyPressEvent: propTypes.func,
    onDrillDown: propTypes.func,
    getDrilldownView: propTypes.func.isRequired,
    scrollRef: propTypes.any,
  }

  var NONE = {}
  function Resources(resources, accessors) {
    return {
      map: function map(fn) {
        if (!resources) return [fn([NONE, null], 0)]
        return resources.map(function(resource, idx) {
          return fn([accessors.resourceId(resource), resource], idx)
        })
      },
      groupEvents: function groupEvents(events) {
        var eventsByResource = new Map()

        if (!resources) {
          // Return all events if resources are not provided
          eventsByResource.set(NONE, events)
          return eventsByResource
        }

        events.forEach(function(event) {
          var id = accessors.resource(event) || NONE
          var resourceEvents = eventsByResource.get(id) || []
          resourceEvents.push(event)
          eventsByResource.set(id, resourceEvents)
        })
        return eventsByResource
      },
    }
  }

  var TimeGrid =
    /*#__PURE__*/
    (function(_Component) {
      _inheritsLoose(TimeGrid, _Component)

      function TimeGrid(props) {
        var _this

        _this = _Component.call(this, props) || this

        _this.handleScroll = function(e) {
          if (_this.scrollRef.current) {
            _this.scrollRef.current.scrollLeft = e.target.scrollLeft
          }
        }

        _this.handleResize = function() {
          cancel(_this.rafHandle)
          _this.rafHandle = request(_this.checkOverflow)
        }

        _this.gutterRef = function(ref) {
          _this.gutter = ref && reactDom.findDOMNode(ref)
        }

        _this.handleSelectAlldayEvent = function() {
          //cancel any pending selections so only the event click goes through.
          _this.clearSelection()

          for (
            var _len = arguments.length, args = new Array(_len), _key = 0;
            _key < _len;
            _key++
          ) {
            args[_key] = arguments[_key]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this.handleSelectAllDaySlot = function(slots, slotInfo) {
          var onSelectSlot = _this.props.onSelectSlot
          notify(onSelectSlot, {
            slots: slots,
            start: slots[0],
            end: slots[slots.length - 1],
            action: slotInfo.action,
            resourceId: slotInfo.resourceId,
          })
        }

        _this.checkOverflow = function() {
          if (_this._updatingOverflow) return
          var content = _this.contentRef.current
          var isOverflowing = content.scrollHeight > content.clientHeight

          if (_this.state.isOverflowing !== isOverflowing) {
            _this._updatingOverflow = true

            _this.setState(
              {
                isOverflowing: isOverflowing,
              },
              function() {
                _this._updatingOverflow = false
              }
            )
          }
        }

        _this.memoizedResources = memoizeOne(function(resources, accessors) {
          return Resources(resources, accessors)
        })
        _this.state = {
          gutterWidth: undefined,
          isOverflowing: null,
        }
        _this.scrollRef = React__default.createRef()
        _this.contentRef = React__default.createRef()
        _this._scrollRatio = null
        return _this
      }

      var _proto = TimeGrid.prototype

      _proto.UNSAFE_componentWillMount = function UNSAFE_componentWillMount() {
        this.calculateScroll()
      }

      _proto.componentDidMount = function componentDidMount() {
        this.checkOverflow()

        if (this.props.width == null) {
          this.measureGutter()
        }

        this.applyScroll()
        window.addEventListener('resize', this.handleResize)
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        window.removeEventListener('resize', this.handleResize)
        cancel(this.rafHandle)

        if (this.measureGutterAnimationFrameRequest) {
          window.cancelAnimationFrame(this.measureGutterAnimationFrameRequest)
        }
      }

      _proto.componentDidUpdate = function componentDidUpdate() {
        if (this.props.width == null) {
          this.measureGutter()
        }

        this.applyScroll() //this.checkOverflow()
      }

      _proto.UNSAFE_componentWillReceiveProps = function UNSAFE_componentWillReceiveProps(
        nextProps
      ) {
        var _this$props = this.props,
          range = _this$props.range,
          scrollToTime = _this$props.scrollToTime // When paginating, reset scroll

        if (
          !eq(nextProps.range[0], range[0], 'minute') ||
          !eq(nextProps.scrollToTime, scrollToTime, 'minute')
        ) {
          this.calculateScroll(nextProps)
        }
      }

      _proto.renderEvents = function renderEvents(
        range,
        events,
        backgroundEvents,
        now
      ) {
        var _this2 = this

        var _this$props2 = this.props,
          min = _this$props2.min,
          max = _this$props2.max,
          components = _this$props2.components,
          accessors = _this$props2.accessors,
          localizer = _this$props2.localizer,
          dayLayoutAlgorithm = _this$props2.dayLayoutAlgorithm
        var resources = this.memoizedResources(this.props.resources, accessors)
        var groupedEvents = resources.groupEvents(events)
        var groupedBackgroundEvents = resources.groupEvents(backgroundEvents)
        return resources.map(function(_ref, i) {
          var id = _ref[0],
            resource = _ref[1]
          return range.map(function(date, jj) {
            var daysEvents = (groupedEvents.get(id) || []).filter(function(
              event
            ) {
              return inRange(
                date,
                accessors.start(event),
                accessors.end(event),
                'day'
              )
            })
            var daysBackgroundEvents = (
              groupedBackgroundEvents.get(id) || []
            ).filter(function(event) {
              return inRange(
                date,
                accessors.start(event),
                accessors.end(event),
                'day'
              )
            })
            return React__default.createElement(
              DayColumn,
              _extends({}, _this2.props, {
                localizer: localizer,
                min: merge(date, min),
                max: merge(date, max),
                resource: resource && id,
                components: components,
                isNow: eq(date, now, 'day'),
                key: i + '-' + jj,
                date: date,
                events: daysEvents,
                backgroundEvents: daysBackgroundEvents,
                dayLayoutAlgorithm: dayLayoutAlgorithm,
              })
            )
          })
        })
      }

      _proto.render = function render() {
        var _this$props3 = this.props,
          events = _this$props3.events,
          backgroundEvents = _this$props3.backgroundEvents,
          range = _this$props3.range,
          width = _this$props3.width,
          rtl = _this$props3.rtl,
          selected = _this$props3.selected,
          getNow = _this$props3.getNow,
          resources = _this$props3.resources,
          components = _this$props3.components,
          accessors = _this$props3.accessors,
          getters = _this$props3.getters,
          localizer = _this$props3.localizer,
          min = _this$props3.min,
          max = _this$props3.max,
          showMultiDayTimes = _this$props3.showMultiDayTimes,
          longPressThreshold = _this$props3.longPressThreshold,
          resizable = _this$props3.resizable
        width = width || this.state.gutterWidth
        var start = range[0],
          end = range[range.length - 1]
        this.slots = range.length
        var allDayEvents = [],
          rangeEvents = [],
          rangeBackgroundEvents = []
        events.forEach(function(event) {
          if (inRange$1(event, start, end, accessors)) {
            var eStart = accessors.start(event),
              eEnd = accessors.end(event)

            if (
              accessors.allDay(event) ||
              (isJustDate(eStart) && isJustDate(eEnd)) ||
              (!showMultiDayTimes && !eq(eStart, eEnd, 'day'))
            ) {
              allDayEvents.push(event)
            } else {
              rangeEvents.push(event)
            }
          }
        })
        backgroundEvents.forEach(function(event) {
          if (inRange$1(event, start, end, accessors)) {
            rangeBackgroundEvents.push(event)
          }
        })
        allDayEvents.sort(function(a, b) {
          return sortEvents(a, b, accessors)
        })
        return React__default.createElement(
          'div',
          {
            className: clsx(
              'rbc-time-view',
              resources && 'rbc-time-view-resources'
            ),
          },
          React__default.createElement(TimeGridHeader, {
            range: range,
            events: allDayEvents,
            width: width,
            rtl: rtl,
            getNow: getNow,
            localizer: localizer,
            selected: selected,
            resources: this.memoizedResources(resources, accessors),
            selectable: this.props.selectable,
            accessors: accessors,
            getters: getters,
            components: components,
            scrollRef: this.scrollRef,
            isOverflowing: this.state.isOverflowing,
            longPressThreshold: longPressThreshold,
            onSelectSlot: this.handleSelectAllDaySlot,
            onSelectEvent: this.handleSelectAlldayEvent,
            onDoubleClickEvent: this.props.onDoubleClickEvent,
            onKeyPressEvent: this.props.onKeyPressEvent,
            onDrillDown: this.props.onDrillDown,
            getDrilldownView: this.props.getDrilldownView,
            resizable: resizable,
          }),
          React__default.createElement(
            'div',
            {
              ref: this.contentRef,
              className: 'rbc-time-content',
              onScroll: this.handleScroll,
            },
            React__default.createElement(TimeGutter, {
              date: start,
              ref: this.gutterRef,
              localizer: localizer,
              min: merge(start, min),
              max: merge(start, max),
              step: this.props.step,
              getNow: this.props.getNow,
              timeslots: this.props.timeslots,
              components: components,
              className: 'rbc-time-gutter',
              getters: getters,
            }),
            this.renderEvents(
              range,
              rangeEvents,
              rangeBackgroundEvents,
              getNow()
            )
          )
        )
      }

      _proto.clearSelection = function clearSelection() {
        clearTimeout(this._selectTimer)
        this._pendingSelection = []
      }

      _proto.measureGutter = function measureGutter() {
        var _this3 = this

        if (this.measureGutterAnimationFrameRequest) {
          window.cancelAnimationFrame(this.measureGutterAnimationFrameRequest)
        }

        this.measureGutterAnimationFrameRequest = window.requestAnimationFrame(
          function() {
            var width = getWidth(_this3.gutter)

            if (width && _this3.state.gutterWidth !== width) {
              _this3.setState({
                gutterWidth: width,
              })
            }
          }
        )
      }

      _proto.applyScroll = function applyScroll() {
        if (this._scrollRatio != null) {
          var content = this.contentRef.current
          content.scrollTop = content.scrollHeight * this._scrollRatio // Only do this once

          this._scrollRatio = null
        }
      }

      _proto.calculateScroll = function calculateScroll(props) {
        if (props === void 0) {
          props = this.props
        }

        var _props = props,
          min = _props.min,
          max = _props.max,
          scrollToTime = _props.scrollToTime
        var diffMillis = scrollToTime - startOf(scrollToTime, 'day')
        var totalMillis = diff(max, min)
        this._scrollRatio = diffMillis / totalMillis
      }

      return TimeGrid
    })(React.Component)
  TimeGrid.propTypes = {
    events: propTypes.array.isRequired,
    backgroundEvents: propTypes.array.isRequired,
    resources: propTypes.array,
    step: propTypes.number,
    timeslots: propTypes.number,
    range: propTypes.arrayOf(propTypes.instanceOf(Date)),
    min: propTypes.instanceOf(Date),
    max: propTypes.instanceOf(Date),
    getNow: propTypes.func.isRequired,
    scrollToTime: propTypes.instanceOf(Date),
    showMultiDayTimes: propTypes.bool,
    rtl: propTypes.bool,
    resizable: propTypes.bool,
    width: propTypes.number,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onNavigate: propTypes.func,
    onSelectSlot: propTypes.func,
    onSelectEnd: propTypes.func,
    onSelectStart: propTypes.func,
    onSelectEvent: propTypes.func,
    onDoubleClickEvent: propTypes.func,
    onKeyPressEvent: propTypes.func,
    onDrillDown: propTypes.func,
    getDrilldownView: propTypes.func.isRequired,
    dayLayoutAlgorithm: DayLayoutAlgorithmPropType,
  }
  TimeGrid.defaultProps = {
    step: 30,
    timeslots: 2,
    min: startOf(new Date(), 'day'),
    max: endOf(new Date(), 'day'),
    scrollToTime: startOf(new Date(), 'day'),
  }

  var Day =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Day, _React$Component)

      function Day() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = Day.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          date = _this$props.date,
          props = _objectWithoutPropertiesLoose(_this$props, ['date'])

        var range = Day.range(date)
        return React__default.createElement(
          TimeGrid,
          _extends({}, props, {
            range: range,
            eventOffset: 10,
          })
        )
      }

      return Day
    })(React__default.Component)

  Day.propTypes = {
    date: propTypes.instanceOf(Date).isRequired,
  }

  Day.range = function(date) {
    return [startOf(date, 'day')]
  }

  Day.navigate = function(date, action) {
    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -1, 'day')

      case navigate.NEXT:
        return add(date, 1, 'day')

      default:
        return date
    }
  }

  Day.title = function(date, _ref) {
    var localizer = _ref.localizer
    return localizer.format(date, 'dayHeaderFormat')
  }

  var Week =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Week, _React$Component)

      function Week() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = Week.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          date = _this$props.date,
          props = _objectWithoutPropertiesLoose(_this$props, ['date'])

        var range = Week.range(date, this.props)
        return React__default.createElement(
          TimeGrid,
          _extends({}, props, {
            range: range,
            eventOffset: 15,
          })
        )
      }

      return Week
    })(React__default.Component)

  Week.propTypes = {
    date: propTypes.instanceOf(Date).isRequired,
  }
  Week.defaultProps = TimeGrid.defaultProps

  Week.navigate = function(date, action) {
    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -1, 'week')

      case navigate.NEXT:
        return add(date, 1, 'week')

      default:
        return date
    }
  }

  Week.range = function(date, _ref) {
    var localizer = _ref.localizer
    var firstOfWeek = localizer.startOfWeek()
    var start = startOf(date, 'week', firstOfWeek)
    var end = endOf(date, 'week', firstOfWeek)
    return range(start, end)
  }

  Week.title = function(date, _ref2) {
    var localizer = _ref2.localizer

    var _Week$range = Week.range(date, {
        localizer: localizer,
      }),
      start = _Week$range[0],
      rest = _Week$range.slice(1)

    return localizer.format(
      {
        start: start,
        end: rest.pop(),
      },
      'dayRangeHeaderFormat'
    )
  }

  function workWeekRange(date, options) {
    return Week.range(date, options).filter(function(d) {
      return [6, 0].indexOf(d.getDay()) === -1
    })
  }

  var WorkWeek =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(WorkWeek, _React$Component)

      function WorkWeek() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = WorkWeek.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          date = _this$props.date,
          props = _objectWithoutPropertiesLoose(_this$props, ['date'])

        var range = workWeekRange(date, this.props)
        return React__default.createElement(
          TimeGrid,
          _extends({}, props, {
            range: range,
            eventOffset: 15,
          })
        )
      }

      return WorkWeek
    })(React__default.Component)

  WorkWeek.propTypes = {
    date: propTypes.instanceOf(Date).isRequired,
  }
  WorkWeek.defaultProps = TimeGrid.defaultProps
  WorkWeek.range = workWeekRange
  WorkWeek.navigate = Week.navigate

  WorkWeek.title = function(date, _ref) {
    var localizer = _ref.localizer

    var _workWeekRange = workWeekRange(date, {
        localizer: localizer,
      }),
      start = _workWeekRange[0],
      rest = _workWeekRange.slice(1)

    return localizer.format(
      {
        start: start,
        end: rest.pop(),
      },
      'dayRangeHeaderFormat'
    )
  }

  function hasClass(element, className) {
    if (element.classList)
      return !!className && element.classList.contains(className)
    return (
      (' ' + (element.className.baseVal || element.className) + ' ').indexOf(
        ' ' + className + ' '
      ) !== -1
    )
  }

  function addClass(element, className) {
    if (element.classList) element.classList.add(className)
    else if (!hasClass(element, className))
      if (typeof element.className === 'string')
        element.className = element.className + ' ' + className
      else
        element.setAttribute(
          'class',
          ((element.className && element.className.baseVal) || '') +
            ' ' +
            className
        )
  }

  function replaceClassName(origClass, classToRemove) {
    return origClass
      .replace(new RegExp('(^|\\s)' + classToRemove + '(?:\\s|$)', 'g'), '$1')
      .replace(/\s+/g, ' ')
      .replace(/^\s*|\s*$/g, '')
  }

  function removeClass(element, className) {
    if (element.classList) {
      element.classList.remove(className)
    } else if (typeof element.className === 'string') {
      element.className = replaceClassName(element.className, className)
    } else {
      element.setAttribute(
        'class',
        replaceClassName(
          (element.className && element.className.baseVal) || '',
          className
        )
      )
    }
  }

  function Agenda(_ref) {
    var selected = _ref.selected,
      getters = _ref.getters,
      accessors = _ref.accessors,
      localizer = _ref.localizer,
      components = _ref.components,
      length = _ref.length,
      date = _ref.date,
      events = _ref.events
    var headerRef = React.useRef(null)
    var dateColRef = React.useRef(null)
    var timeColRef = React.useRef(null)
    var contentRef = React.useRef(null)
    var tbodyRef = React.useRef(null)
    React.useEffect(function() {
      _adjustHeader()
    })

    var renderDay = function renderDay(day, events, dayKey) {
      var Event = components.event,
        AgendaDate = components.date
      events = events.filter(function(e) {
        return inRange$1(e, startOf(day, 'day'), endOf(day, 'day'), accessors)
      })
      return events.map(function(event, idx) {
        var title = accessors.title(event)
        var end = accessors.end(event)
        var start = accessors.start(event)
        var userProps = getters.eventProp(
          event,
          start,
          end,
          isSelected(event, selected)
        )
        var dateLabel = idx === 0 && localizer.format(day, 'agendaDateFormat')
        var first =
          idx === 0
            ? React__default.createElement(
                'td',
                {
                  rowSpan: events.length,
                  className: 'rbc-agenda-date-cell',
                },
                AgendaDate
                  ? React__default.createElement(AgendaDate, {
                      day: day,
                      label: dateLabel,
                    })
                  : dateLabel
              )
            : false
        return React__default.createElement(
          'tr',
          {
            key: dayKey + '_' + idx,
            className: userProps.className,
            style: userProps.style,
          },
          first,
          React__default.createElement(
            'td',
            {
              className: 'rbc-agenda-time-cell',
            },
            timeRangeLabel(day, event)
          ),
          React__default.createElement(
            'td',
            {
              className: 'rbc-agenda-event-cell',
            },
            Event
              ? React__default.createElement(Event, {
                  event: event,
                  title: title,
                })
              : title
          )
        )
      }, [])
    }

    var timeRangeLabel = function timeRangeLabel(day, event) {
      var labelClass = '',
        TimeComponent = components.time,
        label = localizer.messages.allDay
      var end = accessors.end(event)
      var start = accessors.start(event)

      if (!accessors.allDay(event)) {
        if (eq(start, end)) {
          label = localizer.format(start, 'agendaTimeFormat')
        } else if (eq(start, end, 'day')) {
          label = localizer.format(
            {
              start: start,
              end: end,
            },
            'agendaTimeRangeFormat'
          )
        } else if (eq(day, start, 'day')) {
          label = localizer.format(start, 'agendaTimeFormat')
        } else if (eq(day, end, 'day')) {
          label = localizer.format(end, 'agendaTimeFormat')
        }
      }

      if (gt(day, start, 'day')) labelClass = 'rbc-continues-prior'
      if (lt(day, end, 'day')) labelClass += ' rbc-continues-after'
      return React__default.createElement(
        'span',
        {
          className: labelClass.trim(),
        },
        TimeComponent
          ? React__default.createElement(TimeComponent, {
              event: event,
              day: day,
              label: label,
            })
          : label
      )
    }

    var _adjustHeader = function _adjustHeader() {
      if (!tbodyRef.current) return
      var header = headerRef.current
      var firstRow = tbodyRef.current.firstChild
      if (!firstRow) return
      var isOverflowing =
        contentRef.current.scrollHeight > contentRef.current.clientHeight
      var _widths = []
      var widths = _widths
      _widths = [getWidth(firstRow.children[0]), getWidth(firstRow.children[1])]

      if (widths[0] !== _widths[0] || widths[1] !== _widths[1]) {
        dateColRef.current.style.width = _widths[0] + 'px'
        timeColRef.current.style.width = _widths[1] + 'px'
      }

      if (isOverflowing) {
        addClass(header, 'rbc-header-overflowing')
        header.style.marginRight = scrollbarSize() + 'px'
      } else {
        removeClass(header, 'rbc-header-overflowing')
      }
    }

    var messages = localizer.messages
    var end = add(date, length, 'day')
    var range$1 = range(date, end, 'day')
    events = events.filter(function(event) {
      return inRange$1(event, date, end, accessors)
    })
    events.sort(function(a, b) {
      return +accessors.start(a) - +accessors.start(b)
    })
    return React__default.createElement(
      'div',
      {
        className: 'rbc-agenda-view',
      },
      events.length !== 0
        ? React__default.createElement(
            React__default.Fragment,
            null,
            React__default.createElement(
              'table',
              {
                ref: headerRef,
                className: 'rbc-agenda-table',
              },
              React__default.createElement(
                'thead',
                null,
                React__default.createElement(
                  'tr',
                  null,
                  React__default.createElement(
                    'th',
                    {
                      className: 'rbc-header',
                      ref: dateColRef,
                    },
                    messages.date
                  ),
                  React__default.createElement(
                    'th',
                    {
                      className: 'rbc-header',
                      ref: timeColRef,
                    },
                    messages.time
                  ),
                  React__default.createElement(
                    'th',
                    {
                      className: 'rbc-header',
                    },
                    messages.event
                  )
                )
              )
            ),
            React__default.createElement(
              'div',
              {
                className: 'rbc-agenda-content',
                ref: contentRef,
              },
              React__default.createElement(
                'table',
                {
                  className: 'rbc-agenda-table',
                },
                React__default.createElement(
                  'tbody',
                  {
                    ref: tbodyRef,
                  },
                  range$1.map(function(day, idx) {
                    return renderDay(day, events, idx)
                  })
                )
              )
            )
          )
        : React__default.createElement(
            'span',
            {
              className: 'rbc-agenda-empty',
            },
            messages.noEventsInRange
          )
    )
  }

  Agenda.propTypes = {
    events: propTypes.array,
    date: propTypes.instanceOf(Date),
    length: propTypes.number.isRequired,
    selected: propTypes.object,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
  }
  Agenda.defaultProps = {
    length: 30,
  }

  Agenda.range = function(start, _ref2) {
    var _ref2$length = _ref2.length,
      length =
        _ref2$length === void 0 ? Agenda.defaultProps.length : _ref2$length
    var end = add(start, length, 'day')
    return {
      start: start,
      end: end,
    }
  }

  Agenda.navigate = function(date, action, _ref3) {
    var _ref3$length = _ref3.length,
      length =
        _ref3$length === void 0 ? Agenda.defaultProps.length : _ref3$length

    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -length, 'day')

      case navigate.NEXT:
        return add(date, length, 'day')

      default:
        return date
    }
  }

  Agenda.title = function(start, _ref4) {
    var _ref4$length = _ref4.length,
      length =
        _ref4$length === void 0 ? Agenda.defaultProps.length : _ref4$length,
      localizer = _ref4.localizer
    var end = add(start, length, 'day')
    return localizer.format(
      {
        start: start,
        end: end,
      },
      'agendaHeaderFormat'
    )
  }

  var _VIEWS
  var VIEWS = ((_VIEWS = {}),
  (_VIEWS[views.MONTH] = MonthView),
  (_VIEWS[views.WEEK] = Week),
  (_VIEWS[views.WORK_WEEK] = WorkWeek),
  (_VIEWS[views.DAY] = Day),
  (_VIEWS[views.AGENDA] = Agenda),
  _VIEWS)

  function moveDate(View, _ref) {
    var action = _ref.action,
      date = _ref.date,
      today = _ref.today,
      props = _objectWithoutPropertiesLoose(_ref, ['action', 'date', 'today'])

    View = typeof View === 'string' ? VIEWS[View] : View

    switch (action) {
      case navigate.TODAY:
        date = today || new Date()
        break

      case navigate.DATE:
        break

      default:
        !(View && typeof View.navigate === 'function')
          ? invariant_1(
              false,
              'Calendar View components must implement a static `.navigate(date, action)` method.s'
            )
          : void 0
        date = View.navigate(date, action, props)
    }

    return date
  }

  var Toolbar =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Toolbar, _React$Component)

      function Toolbar() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(args)) ||
          this

        _this.navigate = function(action) {
          _this.props.onNavigate(action)
        }

        _this.view = function(view) {
          _this.props.onView(view)
        }

        return _this
      }

      var _proto = Toolbar.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          messages = _this$props.localizer.messages,
          label = _this$props.label
        return React__default.createElement(
          'div',
          {
            className: 'rbc-toolbar',
          },
          React__default.createElement(
            'span',
            {
              className: 'rbc-btn-group',
            },
            React__default.createElement(
              'button',
              {
                type: 'button',
                onClick: this.navigate.bind(null, navigate.TODAY),
              },
              messages.today
            ),
            React__default.createElement(
              'button',
              {
                type: 'button',
                onClick: this.navigate.bind(null, navigate.PREVIOUS),
              },
              messages.previous
            ),
            React__default.createElement(
              'button',
              {
                type: 'button',
                onClick: this.navigate.bind(null, navigate.NEXT),
              },
              messages.next
            )
          ),
          React__default.createElement(
            'span',
            {
              className: 'rbc-toolbar-label',
            },
            label
          ),
          React__default.createElement(
            'span',
            {
              className: 'rbc-btn-group',
            },
            this.viewNamesGroup(messages)
          )
        )
      }

      _proto.viewNamesGroup = function viewNamesGroup(messages) {
        var _this2 = this

        var viewNames = this.props.views
        var view = this.props.view

        if (viewNames.length > 1) {
          return viewNames.map(function(name) {
            return React__default.createElement(
              'button',
              {
                type: 'button',
                key: name,
                className: clsx({
                  'rbc-active': view === name,
                }),
                onClick: _this2.view.bind(null, name),
              },
              messages[name]
            )
          })
        }
      }

      return Toolbar
    })(React__default.Component)

  Toolbar.propTypes = {
    view: propTypes.string.isRequired,
    views: propTypes.arrayOf(propTypes.string).isRequired,
    label: propTypes.node.isRequired,
    localizer: propTypes.object,
    onNavigate: propTypes.func.isRequired,
    onView: propTypes.func.isRequired,
  }

  /**
   * A specialized version of `_.forEach` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns `array`.
   */
  function arrayEach(array, iteratee) {
    var index = -1,
      length = array == null ? 0 : array.length

    while (++index < length) {
      if (iteratee(array[index], index, array) === false) {
        break
      }
    }
    return array
  }

  /**
   * The base implementation of `assignValue` and `assignMergeValue` without
   * value checks.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {string} key The key of the property to assign.
   * @param {*} value The value to assign.
   */
  function baseAssignValue(object, key, value) {
    if (key == '__proto__' && defineProperty) {
      defineProperty(object, key, {
        configurable: true,
        enumerable: true,
        value: value,
        writable: true,
      })
    } else {
      object[key] = value
    }
  }

  /** Used for built-in method references. */
  var objectProto$d = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$b = objectProto$d.hasOwnProperty

  /**
   * Assigns `value` to `key` of `object` if the existing value is not equivalent
   * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {string} key The key of the property to assign.
   * @param {*} value The value to assign.
   */
  function assignValue(object, key, value) {
    var objValue = object[key]
    if (
      !(hasOwnProperty$b.call(object, key) && eq$1(objValue, value)) ||
      (value === undefined && !(key in object))
    ) {
      baseAssignValue(object, key, value)
    }
  }

  /**
   * Copies properties of `source` to `object`.
   *
   * @private
   * @param {Object} source The object to copy properties from.
   * @param {Array} props The property identifiers to copy.
   * @param {Object} [object={}] The object to copy properties to.
   * @param {Function} [customizer] The function to customize copied values.
   * @returns {Object} Returns `object`.
   */
  function copyObject(source, props, object, customizer) {
    var isNew = !object
    object || (object = {})

    var index = -1,
      length = props.length

    while (++index < length) {
      var key = props[index]

      var newValue = customizer
        ? customizer(object[key], source[key], key, object, source)
        : undefined

      if (newValue === undefined) {
        newValue = source[key]
      }
      if (isNew) {
        baseAssignValue(object, key, newValue)
      } else {
        assignValue(object, key, newValue)
      }
    }
    return object
  }

  /**
   * The base implementation of `_.assign` without support for multiple sources
   * or `customizer` functions.
   *
   * @private
   * @param {Object} object The destination object.
   * @param {Object} source The source object.
   * @returns {Object} Returns `object`.
   */
  function baseAssign(object, source) {
    return object && copyObject(source, keys(source), object)
  }

  /**
   * This function is like
   * [`Object.keys`](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
   * except that it includes inherited enumerable properties.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   */
  function nativeKeysIn(object) {
    var result = []
    if (object != null) {
      for (var key in Object(object)) {
        result.push(key)
      }
    }
    return result
  }

  /** Used for built-in method references. */
  var objectProto$e = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$c = objectProto$e.hasOwnProperty

  /**
   * The base implementation of `_.keysIn` which doesn't treat sparse arrays as dense.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   */
  function baseKeysIn(object) {
    if (!isObject(object)) {
      return nativeKeysIn(object)
    }
    var isProto = isPrototype(object),
      result = []

    for (var key in object) {
      if (
        !(
          key == 'constructor' &&
          (isProto || !hasOwnProperty$c.call(object, key))
        )
      ) {
        result.push(key)
      }
    }
    return result
  }

  /**
   * Creates an array of the own and inherited enumerable property names of `object`.
   *
   * **Note:** Non-object values are coerced to objects.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.keysIn(new Foo);
   * // => ['a', 'b', 'c'] (iteration order is not guaranteed)
   */
  function keysIn$1(object) {
    return isArrayLike(object)
      ? arrayLikeKeys(object, true)
      : baseKeysIn(object)
  }

  /**
   * The base implementation of `_.assignIn` without support for multiple sources
   * or `customizer` functions.
   *
   * @private
   * @param {Object} object The destination object.
   * @param {Object} source The source object.
   * @returns {Object} Returns `object`.
   */
  function baseAssignIn(object, source) {
    return object && copyObject(source, keysIn$1(source), object)
  }

  /** Detect free variable `exports`. */
  var freeExports$2 =
    typeof exports == 'object' && exports && !exports.nodeType && exports

  /** Detect free variable `module`. */
  var freeModule$2 =
    freeExports$2 &&
    typeof module == 'object' &&
    module &&
    !module.nodeType &&
    module

  /** Detect the popular CommonJS extension `module.exports`. */
  var moduleExports$2 = freeModule$2 && freeModule$2.exports === freeExports$2

  /** Built-in value references. */
  var Buffer$1 = moduleExports$2 ? root.Buffer : undefined,
    allocUnsafe = Buffer$1 ? Buffer$1.allocUnsafe : undefined

  /**
   * Creates a clone of  `buffer`.
   *
   * @private
   * @param {Buffer} buffer The buffer to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Buffer} Returns the cloned buffer.
   */
  function cloneBuffer(buffer, isDeep) {
    if (isDeep) {
      return buffer.slice()
    }
    var length = buffer.length,
      result = allocUnsafe
        ? allocUnsafe(length)
        : new buffer.constructor(length)

    buffer.copy(result)
    return result
  }

  /**
   * Copies the values of `source` to `array`.
   *
   * @private
   * @param {Array} source The array to copy values from.
   * @param {Array} [array=[]] The array to copy values to.
   * @returns {Array} Returns `array`.
   */
  function copyArray(source, array) {
    var index = -1,
      length = source.length

    array || (array = Array(length))
    while (++index < length) {
      array[index] = source[index]
    }
    return array
  }

  /**
   * Copies own symbols of `source` to `object`.
   *
   * @private
   * @param {Object} source The object to copy symbols from.
   * @param {Object} [object={}] The object to copy symbols to.
   * @returns {Object} Returns `object`.
   */
  function copySymbols(source, object) {
    return copyObject(source, getSymbols(source), object)
  }

  /** Built-in value references. */
  var getPrototype = overArg(Object.getPrototypeOf, Object)

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeGetSymbols$1 = Object.getOwnPropertySymbols

  /**
   * Creates an array of the own and inherited enumerable symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of symbols.
   */
  var getSymbolsIn = !nativeGetSymbols$1
    ? stubArray
    : function(object) {
        var result = []
        while (object) {
          arrayPush(result, getSymbols(object))
          object = getPrototype(object)
        }
        return result
      }

  /**
   * Copies own and inherited symbols of `source` to `object`.
   *
   * @private
   * @param {Object} source The object to copy symbols from.
   * @param {Object} [object={}] The object to copy symbols to.
   * @returns {Object} Returns `object`.
   */
  function copySymbolsIn(source, object) {
    return copyObject(source, getSymbolsIn(source), object)
  }

  /**
   * Creates an array of own and inherited enumerable property names and
   * symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names and symbols.
   */
  function getAllKeysIn(object) {
    return baseGetAllKeys(object, keysIn$1, getSymbolsIn)
  }

  /** Used for built-in method references. */
  var objectProto$f = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$d = objectProto$f.hasOwnProperty

  /**
   * Initializes an array clone.
   *
   * @private
   * @param {Array} array The array to clone.
   * @returns {Array} Returns the initialized clone.
   */
  function initCloneArray(array) {
    var length = array.length,
      result = new array.constructor(length)

    // Add properties assigned by `RegExp#exec`.
    if (
      length &&
      typeof array[0] == 'string' &&
      hasOwnProperty$d.call(array, 'index')
    ) {
      result.index = array.index
      result.input = array.input
    }
    return result
  }

  /**
   * Creates a clone of `arrayBuffer`.
   *
   * @private
   * @param {ArrayBuffer} arrayBuffer The array buffer to clone.
   * @returns {ArrayBuffer} Returns the cloned array buffer.
   */
  function cloneArrayBuffer(arrayBuffer) {
    var result = new arrayBuffer.constructor(arrayBuffer.byteLength)
    new Uint8Array(result).set(new Uint8Array(arrayBuffer))
    return result
  }

  /**
   * Creates a clone of `dataView`.
   *
   * @private
   * @param {Object} dataView The data view to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Object} Returns the cloned data view.
   */
  function cloneDataView(dataView, isDeep) {
    var buffer = isDeep ? cloneArrayBuffer(dataView.buffer) : dataView.buffer
    return new dataView.constructor(
      buffer,
      dataView.byteOffset,
      dataView.byteLength
    )
  }

  /** Used to match `RegExp` flags from their coerced string values. */
  var reFlags = /\w*$/

  /**
   * Creates a clone of `regexp`.
   *
   * @private
   * @param {Object} regexp The regexp to clone.
   * @returns {Object} Returns the cloned regexp.
   */
  function cloneRegExp(regexp) {
    var result = new regexp.constructor(regexp.source, reFlags.exec(regexp))
    result.lastIndex = regexp.lastIndex
    return result
  }

  /** Used to convert symbols to primitives and strings. */
  var symbolProto$2 = Symbol$1 ? Symbol$1.prototype : undefined,
    symbolValueOf$1 = symbolProto$2 ? symbolProto$2.valueOf : undefined

  /**
   * Creates a clone of the `symbol` object.
   *
   * @private
   * @param {Object} symbol The symbol object to clone.
   * @returns {Object} Returns the cloned symbol object.
   */
  function cloneSymbol(symbol) {
    return symbolValueOf$1 ? Object(symbolValueOf$1.call(symbol)) : {}
  }

  /**
   * Creates a clone of `typedArray`.
   *
   * @private
   * @param {Object} typedArray The typed array to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Object} Returns the cloned typed array.
   */
  function cloneTypedArray(typedArray, isDeep) {
    var buffer = isDeep
      ? cloneArrayBuffer(typedArray.buffer)
      : typedArray.buffer
    return new typedArray.constructor(
      buffer,
      typedArray.byteOffset,
      typedArray.length
    )
  }

  /** `Object#toString` result references. */
  var boolTag$2 = '[object Boolean]',
    dateTag$2 = '[object Date]',
    mapTag$3 = '[object Map]',
    numberTag$2 = '[object Number]',
    regexpTag$2 = '[object RegExp]',
    setTag$3 = '[object Set]',
    stringTag$2 = '[object String]',
    symbolTag$2 = '[object Symbol]'

  var arrayBufferTag$2 = '[object ArrayBuffer]',
    dataViewTag$3 = '[object DataView]',
    float32Tag$1 = '[object Float32Array]',
    float64Tag$1 = '[object Float64Array]',
    int8Tag$1 = '[object Int8Array]',
    int16Tag$1 = '[object Int16Array]',
    int32Tag$1 = '[object Int32Array]',
    uint8Tag$1 = '[object Uint8Array]',
    uint8ClampedTag$1 = '[object Uint8ClampedArray]',
    uint16Tag$1 = '[object Uint16Array]',
    uint32Tag$1 = '[object Uint32Array]'

  /**
   * Initializes an object clone based on its `toStringTag`.
   *
   * **Note:** This function only supports cloning values with tags of
   * `Boolean`, `Date`, `Error`, `Map`, `Number`, `RegExp`, `Set`, or `String`.
   *
   * @private
   * @param {Object} object The object to clone.
   * @param {string} tag The `toStringTag` of the object to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Object} Returns the initialized clone.
   */
  function initCloneByTag(object, tag, isDeep) {
    var Ctor = object.constructor
    switch (tag) {
      case arrayBufferTag$2:
        return cloneArrayBuffer(object)

      case boolTag$2:
      case dateTag$2:
        return new Ctor(+object)

      case dataViewTag$3:
        return cloneDataView(object, isDeep)

      case float32Tag$1:
      case float64Tag$1:
      case int8Tag$1:
      case int16Tag$1:
      case int32Tag$1:
      case uint8Tag$1:
      case uint8ClampedTag$1:
      case uint16Tag$1:
      case uint32Tag$1:
        return cloneTypedArray(object, isDeep)

      case mapTag$3:
        return new Ctor()

      case numberTag$2:
      case stringTag$2:
        return new Ctor(object)

      case regexpTag$2:
        return cloneRegExp(object)

      case setTag$3:
        return new Ctor()

      case symbolTag$2:
        return cloneSymbol(object)
    }
  }

  /** Built-in value references. */
  var objectCreate = Object.create

  /**
   * The base implementation of `_.create` without support for assigning
   * properties to the created object.
   *
   * @private
   * @param {Object} proto The object to inherit from.
   * @returns {Object} Returns the new object.
   */
  var baseCreate = (function() {
    function object() {}
    return function(proto) {
      if (!isObject(proto)) {
        return {}
      }
      if (objectCreate) {
        return objectCreate(proto)
      }
      object.prototype = proto
      var result = new object()
      object.prototype = undefined
      return result
    }
  })()

  /**
   * Initializes an object clone.
   *
   * @private
   * @param {Object} object The object to clone.
   * @returns {Object} Returns the initialized clone.
   */
  function initCloneObject(object) {
    return typeof object.constructor == 'function' && !isPrototype(object)
      ? baseCreate(getPrototype(object))
      : {}
  }

  /** `Object#toString` result references. */
  var mapTag$4 = '[object Map]'

  /**
   * The base implementation of `_.isMap` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a map, else `false`.
   */
  function baseIsMap(value) {
    return isObjectLike(value) && getTag$1(value) == mapTag$4
  }

  /* Node.js helper references. */
  var nodeIsMap = nodeUtil && nodeUtil.isMap

  /**
   * Checks if `value` is classified as a `Map` object.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a map, else `false`.
   * @example
   *
   * _.isMap(new Map);
   * // => true
   *
   * _.isMap(new WeakMap);
   * // => false
   */
  var isMap = nodeIsMap ? baseUnary(nodeIsMap) : baseIsMap

  /** `Object#toString` result references. */
  var setTag$4 = '[object Set]'

  /**
   * The base implementation of `_.isSet` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a set, else `false`.
   */
  function baseIsSet(value) {
    return isObjectLike(value) && getTag$1(value) == setTag$4
  }

  /* Node.js helper references. */
  var nodeIsSet = nodeUtil && nodeUtil.isSet

  /**
   * Checks if `value` is classified as a `Set` object.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a set, else `false`.
   * @example
   *
   * _.isSet(new Set);
   * // => true
   *
   * _.isSet(new WeakSet);
   * // => false
   */
  var isSet = nodeIsSet ? baseUnary(nodeIsSet) : baseIsSet

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG = 1,
    CLONE_FLAT_FLAG = 2,
    CLONE_SYMBOLS_FLAG = 4

  /** `Object#toString` result references. */
  var argsTag$3 = '[object Arguments]',
    arrayTag$2 = '[object Array]',
    boolTag$3 = '[object Boolean]',
    dateTag$3 = '[object Date]',
    errorTag$2 = '[object Error]',
    funcTag$3 = '[object Function]',
    genTag$1 = '[object GeneratorFunction]',
    mapTag$5 = '[object Map]',
    numberTag$3 = '[object Number]',
    objectTag$3 = '[object Object]',
    regexpTag$3 = '[object RegExp]',
    setTag$5 = '[object Set]',
    stringTag$3 = '[object String]',
    symbolTag$3 = '[object Symbol]',
    weakMapTag$2 = '[object WeakMap]'

  var arrayBufferTag$3 = '[object ArrayBuffer]',
    dataViewTag$4 = '[object DataView]',
    float32Tag$2 = '[object Float32Array]',
    float64Tag$2 = '[object Float64Array]',
    int8Tag$2 = '[object Int8Array]',
    int16Tag$2 = '[object Int16Array]',
    int32Tag$2 = '[object Int32Array]',
    uint8Tag$2 = '[object Uint8Array]',
    uint8ClampedTag$2 = '[object Uint8ClampedArray]',
    uint16Tag$2 = '[object Uint16Array]',
    uint32Tag$2 = '[object Uint32Array]'

  /** Used to identify `toStringTag` values supported by `_.clone`. */
  var cloneableTags = {}
  cloneableTags[argsTag$3] = cloneableTags[arrayTag$2] = cloneableTags[
    arrayBufferTag$3
  ] = cloneableTags[dataViewTag$4] = cloneableTags[boolTag$3] = cloneableTags[
    dateTag$3
  ] = cloneableTags[float32Tag$2] = cloneableTags[float64Tag$2] = cloneableTags[
    int8Tag$2
  ] = cloneableTags[int16Tag$2] = cloneableTags[int32Tag$2] = cloneableTags[
    mapTag$5
  ] = cloneableTags[numberTag$3] = cloneableTags[objectTag$3] = cloneableTags[
    regexpTag$3
  ] = cloneableTags[setTag$5] = cloneableTags[stringTag$3] = cloneableTags[
    symbolTag$3
  ] = cloneableTags[uint8Tag$2] = cloneableTags[
    uint8ClampedTag$2
  ] = cloneableTags[uint16Tag$2] = cloneableTags[uint32Tag$2] = true
  cloneableTags[errorTag$2] = cloneableTags[funcTag$3] = cloneableTags[
    weakMapTag$2
  ] = false

  /**
   * The base implementation of `_.clone` and `_.cloneDeep` which tracks
   * traversed objects.
   *
   * @private
   * @param {*} value The value to clone.
   * @param {boolean} bitmask The bitmask flags.
   *  1 - Deep clone
   *  2 - Flatten inherited properties
   *  4 - Clone symbols
   * @param {Function} [customizer] The function to customize cloning.
   * @param {string} [key] The key of `value`.
   * @param {Object} [object] The parent object of `value`.
   * @param {Object} [stack] Tracks traversed objects and their clone counterparts.
   * @returns {*} Returns the cloned value.
   */
  function baseClone(value, bitmask, customizer, key, object, stack) {
    var result,
      isDeep = bitmask & CLONE_DEEP_FLAG,
      isFlat = bitmask & CLONE_FLAT_FLAG,
      isFull = bitmask & CLONE_SYMBOLS_FLAG

    if (customizer) {
      result = object
        ? customizer(value, key, object, stack)
        : customizer(value)
    }
    if (result !== undefined) {
      return result
    }
    if (!isObject(value)) {
      return value
    }
    var isArr = isArray(value)
    if (isArr) {
      result = initCloneArray(value)
      if (!isDeep) {
        return copyArray(value, result)
      }
    } else {
      var tag = getTag$1(value),
        isFunc = tag == funcTag$3 || tag == genTag$1

      if (isBuffer(value)) {
        return cloneBuffer(value, isDeep)
      }
      if (tag == objectTag$3 || tag == argsTag$3 || (isFunc && !object)) {
        result = isFlat || isFunc ? {} : initCloneObject(value)
        if (!isDeep) {
          return isFlat
            ? copySymbolsIn(value, baseAssignIn(result, value))
            : copySymbols(value, baseAssign(result, value))
        }
      } else {
        if (!cloneableTags[tag]) {
          return object ? value : {}
        }
        result = initCloneByTag(value, tag, isDeep)
      }
    }
    // Check for circular references and return its corresponding clone.
    stack || (stack = new Stack())
    var stacked = stack.get(value)
    if (stacked) {
      return stacked
    }
    stack.set(value, result)

    if (isSet(value)) {
      value.forEach(function(subValue) {
        result.add(
          baseClone(subValue, bitmask, customizer, subValue, value, stack)
        )
      })

      return result
    }

    if (isMap(value)) {
      value.forEach(function(subValue, key) {
        result.set(
          key,
          baseClone(subValue, bitmask, customizer, key, value, stack)
        )
      })

      return result
    }

    var keysFunc = isFull
      ? isFlat
        ? getAllKeysIn
        : getAllKeys
      : isFlat
      ? keysIn
      : keys

    var props = isArr ? undefined : keysFunc(value)
    arrayEach(props || value, function(subValue, key) {
      if (props) {
        key = subValue
        subValue = value[key]
      }
      // Recursively populate clone (susceptible to call stack limits).
      assignValue(
        result,
        key,
        baseClone(subValue, bitmask, customizer, key, value, stack)
      )
    })
    return result
  }

  /**
   * Gets the last element of `array`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to query.
   * @returns {*} Returns the last element of `array`.
   * @example
   *
   * _.last([1, 2, 3]);
   * // => 3
   */
  function last(array) {
    var length = array == null ? 0 : array.length
    return length ? array[length - 1] : undefined
  }

  /**
   * Gets the parent value at `path` of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array} path The path to get the parent value of.
   * @returns {*} Returns the parent value.
   */
  function parent(object, path) {
    return path.length < 2 ? object : baseGet(object, baseSlice(path, 0, -1))
  }

  /**
   * The base implementation of `_.unset`.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {Array|string} path The property path to unset.
   * @returns {boolean} Returns `true` if the property is deleted, else `false`.
   */
  function baseUnset(object, path) {
    path = castPath(path, object)
    object = parent(object, path)
    return object == null || delete object[toKey(last(path))]
  }

  /** `Object#toString` result references. */
  var objectTag$4 = '[object Object]'

  /** Used for built-in method references. */
  var funcProto$2 = Function.prototype,
    objectProto$g = Object.prototype

  /** Used to resolve the decompiled source of functions. */
  var funcToString$2 = funcProto$2.toString

  /** Used to check objects for own properties. */
  var hasOwnProperty$e = objectProto$g.hasOwnProperty

  /** Used to infer the `Object` constructor. */
  var objectCtorString = funcToString$2.call(Object)

  /**
   * Checks if `value` is a plain object, that is, an object created by the
   * `Object` constructor or one with a `[[Prototype]]` of `null`.
   *
   * @static
   * @memberOf _
   * @since 0.8.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a plain object, else `false`.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   * }
   *
   * _.isPlainObject(new Foo);
   * // => false
   *
   * _.isPlainObject([1, 2, 3]);
   * // => false
   *
   * _.isPlainObject({ 'x': 0, 'y': 0 });
   * // => true
   *
   * _.isPlainObject(Object.create(null));
   * // => true
   */
  function isPlainObject(value) {
    if (!isObjectLike(value) || baseGetTag(value) != objectTag$4) {
      return false
    }
    var proto = getPrototype(value)
    if (proto === null) {
      return true
    }
    var Ctor = hasOwnProperty$e.call(proto, 'constructor') && proto.constructor
    return (
      typeof Ctor == 'function' &&
      Ctor instanceof Ctor &&
      funcToString$2.call(Ctor) == objectCtorString
    )
  }

  /**
   * Used by `_.omit` to customize its `_.cloneDeep` use to only clone plain
   * objects.
   *
   * @private
   * @param {*} value The value to inspect.
   * @param {string} key The key of the property to inspect.
   * @returns {*} Returns the uncloned value or `undefined` to defer cloning to `_.cloneDeep`.
   */
  function customOmitClone(value) {
    return isPlainObject(value) ? undefined : value
  }

  /**
   * Flattens `array` a single level deep.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to flatten.
   * @returns {Array} Returns the new flattened array.
   * @example
   *
   * _.flatten([1, [2, [3, [4]], 5]]);
   * // => [1, 2, [3, [4]], 5]
   */
  function flatten(array) {
    var length = array == null ? 0 : array.length
    return length ? baseFlatten(array, 1) : []
  }

  /**
   * A specialized version of `baseRest` which flattens the rest array.
   *
   * @private
   * @param {Function} func The function to apply a rest parameter to.
   * @returns {Function} Returns the new function.
   */
  function flatRest(func) {
    return setToString(overRest(func, undefined, flatten), func + '')
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$1 = 1,
    CLONE_FLAT_FLAG$1 = 2,
    CLONE_SYMBOLS_FLAG$1 = 4

  /**
   * The opposite of `_.pick`; this method creates an object composed of the
   * own and inherited enumerable property paths of `object` that are not omitted.
   *
   * **Note:** This method is considerably slower than `_.pick`.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The source object.
   * @param {...(string|string[])} [paths] The property paths to omit.
   * @returns {Object} Returns the new object.
   * @example
   *
   * var object = { 'a': 1, 'b': '2', 'c': 3 };
   *
   * _.omit(object, ['a', 'c']);
   * // => { 'b': '2' }
   */
  var omit = flatRest(function(object, paths) {
    var result = {}
    if (object == null) {
      return result
    }
    var isDeep = false
    paths = arrayMap(paths, function(path) {
      path = castPath(path, object)
      isDeep || (isDeep = path.length > 1)
      return path
    })
    copyObject(object, getAllKeysIn(object), result)
    if (isDeep) {
      result = baseClone(
        result,
        CLONE_DEEP_FLAG$1 | CLONE_FLAT_FLAG$1 | CLONE_SYMBOLS_FLAG$1,
        customOmitClone
      )
    }
    var length = paths.length
    while (length--) {
      baseUnset(result, paths[length])
    }
    return result
  })

  /** Used for built-in method references. */
  var objectProto$h = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$f = objectProto$h.hasOwnProperty

  /**
   * Assigns own and inherited enumerable string keyed properties of source
   * objects to the destination object for all destination properties that
   * resolve to `undefined`. Source objects are applied from left to right.
   * Once a property is set, additional values of the same property are ignored.
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} [sources] The source objects.
   * @returns {Object} Returns `object`.
   * @see _.defaultsDeep
   * @example
   *
   * _.defaults({ 'a': 1 }, { 'b': 2 }, { 'a': 3 });
   * // => { 'a': 1, 'b': 2 }
   */
  var defaults = baseRest(function(object, sources) {
    object = Object(object)

    var index = -1
    var length = sources.length
    var guard = length > 2 ? sources[2] : undefined

    if (guard && isIterateeCall(sources[0], sources[1], guard)) {
      length = 1
    }

    while (++index < length) {
      var source = sources[index]
      var props = keysIn$1(source)
      var propsIndex = -1
      var propsLength = props.length

      while (++propsIndex < propsLength) {
        var key = props[propsIndex]
        var value = object[key]

        if (
          value === undefined ||
          (eq$1(value, objectProto$h[key]) &&
            !hasOwnProperty$f.call(object, key))
        ) {
          object[key] = source[key]
        }
      }
    }

    return object
  })

  /**
   * An alternative to `_.reduce`; this method transforms `object` to a new
   * `accumulator` object which is the result of running each of its own
   * enumerable string keyed properties thru `iteratee`, with each invocation
   * potentially mutating the `accumulator` object. If `accumulator` is not
   * provided, a new object with the same `[[Prototype]]` will be used. The
   * iteratee is invoked with four arguments: (accumulator, value, key, object).
   * Iteratee functions may exit iteration early by explicitly returning `false`.
   *
   * @static
   * @memberOf _
   * @since 1.3.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @param {*} [accumulator] The custom accumulator value.
   * @returns {*} Returns the accumulated value.
   * @example
   *
   * _.transform([2, 3, 4], function(result, n) {
   *   result.push(n *= n);
   *   return n % 2 == 0;
   * }, []);
   * // => [4, 9]
   *
   * _.transform({ 'a': 1, 'b': 2, 'c': 1 }, function(result, value, key) {
   *   (result[value] || (result[value] = [])).push(key);
   * }, {});
   * // => { '1': ['a', 'c'], '2': ['b'] }
   */
  function transform(object, iteratee, accumulator) {
    var isArr = isArray(object),
      isArrLike = isArr || isBuffer(object) || isTypedArray(object)

    iteratee = baseIteratee(iteratee, 4)
    if (accumulator == null) {
      var Ctor = object && object.constructor
      if (isArrLike) {
        accumulator = isArr ? new Ctor() : []
      } else if (isObject(object)) {
        accumulator = isFunction(Ctor) ? baseCreate(getPrototype(object)) : {}
      } else {
        accumulator = {}
      }
    }
    ;(isArrLike
      ? arrayEach
      : baseForOwn)(object, function(value, index, object) {
      return iteratee(accumulator, value, index, object)
    })
    return accumulator
  }

  /**
   * Creates an object with the same keys as `object` and values generated
   * by running each own enumerable string keyed property of `object` thru
   * `iteratee`. The iteratee is invoked with three arguments:
   * (value, key, object).
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Object} Returns the new mapped object.
   * @see _.mapKeys
   * @example
   *
   * var users = {
   *   'fred':    { 'user': 'fred',    'age': 40 },
   *   'pebbles': { 'user': 'pebbles', 'age': 1 }
   * };
   *
   * _.mapValues(users, function(o) { return o.age; });
   * // => { 'fred': 40, 'pebbles': 1 } (iteration order is not guaranteed)
   *
   * // The `_.property` iteratee shorthand.
   * _.mapValues(users, 'age');
   * // => { 'fred': 40, 'pebbles': 1 } (iteration order is not guaranteed)
   */
  function mapValues(object, iteratee) {
    var result = {}
    iteratee = baseIteratee(iteratee, 3)

    baseForOwn(object, function(value, key, object) {
      baseAssignValue(result, key, iteratee(value, key, object))
    })
    return result
  }

  /**
   * Retrieve via an accessor-like property
   *
   *    accessor(obj, 'name')   // => retrieves obj['name']
   *    accessor(data, func)    // => retrieves func(data)
   *    ... otherwise null
   */
  function accessor$1(data, field) {
    var value = null
    if (typeof field === 'function') value = field(data)
    else if (
      typeof field === 'string' &&
      typeof data === 'object' &&
      data != null &&
      field in data
    )
      value = data[field]
    return value
  }
  var wrapAccessor = function wrapAccessor(acc) {
    return function(data) {
      return accessor$1(data, acc)
    }
  }

  function viewNames$1(_views) {
    return !Array.isArray(_views) ? Object.keys(_views) : _views
  }

  function isValidView(view, _ref) {
    var _views = _ref.views
    var names = viewNames$1(_views)
    return names.indexOf(view) !== -1
  }
  /**
   * react-big-calendar is a full featured Calendar component for managing events and dates. It uses
   * modern `flexbox` for layout, making it super responsive and performant. Leaving most of the layout heavy lifting
   * to the browser. __note:__ The default styles use `height: 100%` which means your container must set an explicit
   * height (feel free to adjust the styles to suit your specific needs).
   *
   * Big Calendar is unopiniated about editing and moving events, preferring to let you implement it in a way that makes
   * the most sense to your app. It also tries not to be prescriptive about your event data structures, just tell it
   * how to find the start and end datetimes and you can pass it whatever you want.
   *
   * One thing to note is that, `react-big-calendar` treats event start/end dates as an _exclusive_ range.
   * which means that the event spans up to, but not including, the end date. In the case
   * of displaying events on whole days, end dates are rounded _up_ to the next day. So an
   * event ending on `Apr 8th 12:00:00 am` will not appear on the 8th, whereas one ending
   * on `Apr 8th 12:01:00 am` will. If you want _inclusive_ ranges consider providing a
   * function `endAccessor` that returns the end date + 1 day for those events that end at midnight.
   */

  var Calendar =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Calendar, _React$Component)

      function Calendar() {
        var _this

        for (
          var _len = arguments.length, _args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          _args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(_args)) ||
          this

        _this.getViews = function() {
          var views = _this.props.views

          if (Array.isArray(views)) {
            return transform(
              views,
              function(obj, name) {
                return (obj[name] = VIEWS[name])
              },
              {}
            )
          }

          if (typeof views === 'object') {
            return mapValues(views, function(value, key) {
              if (value === true) {
                return VIEWS[key]
              }

              return value
            })
          }

          return VIEWS
        }

        _this.getView = function() {
          var views = _this.getViews()

          return views[_this.props.view]
        }

        _this.getDrilldownView = function(date) {
          var _this$props = _this.props,
            view = _this$props.view,
            drilldownView = _this$props.drilldownView,
            getDrilldownView = _this$props.getDrilldownView
          if (!getDrilldownView) return drilldownView
          return getDrilldownView(date, view, Object.keys(_this.getViews()))
        }

        _this.handleRangeChange = function(date, viewComponent, view) {
          var _this$props2 = _this.props,
            onRangeChange = _this$props2.onRangeChange,
            localizer = _this$props2.localizer

          if (onRangeChange) {
            if (viewComponent.range) {
              onRangeChange(
                viewComponent.range(date, {
                  localizer: localizer,
                }),
                view
              )
            } else {
              {
                console.error('onRangeChange prop not supported for this view')
              }
            }
          }
        }

        _this.handleNavigate = function(action, newDate) {
          var _this$props3 = _this.props,
            view = _this$props3.view,
            date = _this$props3.date,
            getNow = _this$props3.getNow,
            onNavigate = _this$props3.onNavigate,
            props = _objectWithoutPropertiesLoose(_this$props3, [
              'view',
              'date',
              'getNow',
              'onNavigate',
            ])

          var ViewComponent = _this.getView()

          var today = getNow()
          date = moveDate(
            ViewComponent,
            _extends({}, props, {
              action: action,
              date: newDate || date || today,
              today: today,
            })
          )
          onNavigate(date, view, action)

          _this.handleRangeChange(date, ViewComponent)
        }

        _this.handleViewChange = function(view) {
          if (view !== _this.props.view && isValidView(view, _this.props)) {
            _this.props.onView(view)
          }

          var views = _this.getViews()

          _this.handleRangeChange(
            _this.props.date || _this.props.getNow(),
            views[view],
            view
          )
        }

        _this.handleSelectEvent = function() {
          for (
            var _len2 = arguments.length, args = new Array(_len2), _key2 = 0;
            _key2 < _len2;
            _key2++
          ) {
            args[_key2] = arguments[_key2]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this.handleDoubleClickEvent = function() {
          for (
            var _len3 = arguments.length, args = new Array(_len3), _key3 = 0;
            _key3 < _len3;
            _key3++
          ) {
            args[_key3] = arguments[_key3]
          }

          notify(_this.props.onDoubleClickEvent, args)
        }

        _this.handleKeyPressEvent = function() {
          for (
            var _len4 = arguments.length, args = new Array(_len4), _key4 = 0;
            _key4 < _len4;
            _key4++
          ) {
            args[_key4] = arguments[_key4]
          }

          notify(_this.props.onKeyPressEvent, args)
        }

        _this.handleSelectSlot = function(slotInfo) {
          notify(_this.props.onSelectSlot, slotInfo)
        }

        _this.handleDrillDown = function(date, view) {
          var onDrillDown = _this.props.onDrillDown

          if (onDrillDown) {
            onDrillDown(date, view, _this.drilldownView)
            return
          }

          if (view) _this.handleViewChange(view)

          _this.handleNavigate(navigate.DATE, date)
        }

        _this.state = {
          context: _this.getContext(_this.props),
        }
        return _this
      }

      var _proto = Calendar.prototype

      _proto.UNSAFE_componentWillReceiveProps = function UNSAFE_componentWillReceiveProps(
        nextProps
      ) {
        this.setState({
          context: this.getContext(nextProps),
        })
      }

      _proto.getContext = function getContext(_ref2) {
        var startAccessor = _ref2.startAccessor,
          endAccessor = _ref2.endAccessor,
          allDayAccessor = _ref2.allDayAccessor,
          tooltipAccessor = _ref2.tooltipAccessor,
          titleAccessor = _ref2.titleAccessor,
          resourceAccessor = _ref2.resourceAccessor,
          resourceIdAccessor = _ref2.resourceIdAccessor,
          resourceTitleAccessor = _ref2.resourceTitleAccessor,
          eventPropGetter = _ref2.eventPropGetter,
          backgroundEventPropGetter = _ref2.backgroundEventPropGetter,
          slotPropGetter = _ref2.slotPropGetter,
          slotGroupPropGetter = _ref2.slotGroupPropGetter,
          dayPropGetter = _ref2.dayPropGetter,
          view = _ref2.view,
          views = _ref2.views,
          localizer = _ref2.localizer,
          culture = _ref2.culture,
          _ref2$messages = _ref2.messages,
          messages$1 = _ref2$messages === void 0 ? {} : _ref2$messages,
          _ref2$components = _ref2.components,
          components = _ref2$components === void 0 ? {} : _ref2$components,
          _ref2$formats = _ref2.formats,
          formats = _ref2$formats === void 0 ? {} : _ref2$formats
        var names = viewNames$1(views)
        var msgs = messages(messages$1)
        return {
          viewNames: names,
          localizer: mergeWithDefaults(localizer, culture, formats, msgs),
          getters: {
            eventProp: function eventProp() {
              return (
                (eventPropGetter && eventPropGetter.apply(void 0, arguments)) ||
                {}
              )
            },
            backgroundEventProp: function backgroundEventProp() {
              return (
                (backgroundEventPropGetter &&
                  backgroundEventPropGetter.apply(void 0, arguments)) ||
                {}
              )
            },
            slotProp: function slotProp() {
              return (
                (slotPropGetter && slotPropGetter.apply(void 0, arguments)) ||
                {}
              )
            },
            slotGroupProp: function slotGroupProp() {
              return (
                (slotGroupPropGetter &&
                  slotGroupPropGetter.apply(void 0, arguments)) ||
                {}
              )
            },
            dayProp: function dayProp() {
              return (
                (dayPropGetter && dayPropGetter.apply(void 0, arguments)) || {}
              )
            },
          },
          components: defaults(
            components[view] || {},
            omit(components, names),
            {
              eventWrapper: NoopWrapper,
              backgroundEventWrapper: NoopWrapper,
              eventContainerWrapper: NoopWrapper,
              dateCellWrapper: NoopWrapper,
              weekWrapper: NoopWrapper,
              timeSlotWrapper: NoopWrapper,
            }
          ),
          accessors: {
            start: wrapAccessor(startAccessor),
            end: wrapAccessor(endAccessor),
            allDay: wrapAccessor(allDayAccessor),
            tooltip: wrapAccessor(tooltipAccessor),
            title: wrapAccessor(titleAccessor),
            resource: wrapAccessor(resourceAccessor),
            resourceId: wrapAccessor(resourceIdAccessor),
            resourceTitle: wrapAccessor(resourceTitleAccessor),
          },
        }
      }

      _proto.render = function render() {
        var _this$props4 = this.props,
          view = _this$props4.view,
          toolbar = _this$props4.toolbar,
          events = _this$props4.events,
          _this$props4$backgrou = _this$props4.backgroundEvents,
          backgroundEvents =
            _this$props4$backgrou === void 0 ? [] : _this$props4$backgrou,
          style = _this$props4.style,
          className = _this$props4.className,
          elementProps = _this$props4.elementProps,
          current = _this$props4.date,
          getNow = _this$props4.getNow,
          length = _this$props4.length,
          showMultiDayTimes = _this$props4.showMultiDayTimes,
          onShowMore = _this$props4.onShowMore,
          _0 = _this$props4.components,
          _1 = _this$props4.formats,
          _2 = _this$props4.messages,
          _3 = _this$props4.culture,
          props = _objectWithoutPropertiesLoose(_this$props4, [
            'view',
            'toolbar',
            'events',
            'backgroundEvents',
            'style',
            'className',
            'elementProps',
            'date',
            'getNow',
            'length',
            'showMultiDayTimes',
            'onShowMore',
            'components',
            'formats',
            'messages',
            'culture',
          ])

        current = current || getNow()
        var View = this.getView()
        var _this$state$context = this.state.context,
          accessors = _this$state$context.accessors,
          components = _this$state$context.components,
          getters = _this$state$context.getters,
          localizer = _this$state$context.localizer,
          viewNames = _this$state$context.viewNames
        var CalToolbar = components.toolbar || Toolbar
        var label = View.title(current, {
          localizer: localizer,
          length: length,
        })
        return React__default.createElement(
          'div',
          _extends({}, elementProps, {
            className: clsx(className, 'rbc-calendar', props.rtl && 'rbc-rtl'),
            style: style,
          }),
          toolbar &&
            React__default.createElement(CalToolbar, {
              date: current,
              view: view,
              views: viewNames,
              label: label,
              onView: this.handleViewChange,
              onNavigate: this.handleNavigate,
              localizer: localizer,
            }),
          React__default.createElement(
            View,
            _extends({}, props, {
              events: events,
              backgroundEvents: backgroundEvents,
              date: current,
              getNow: getNow,
              length: length,
              localizer: localizer,
              getters: getters,
              components: components,
              accessors: accessors,
              showMultiDayTimes: showMultiDayTimes,
              getDrilldownView: this.getDrilldownView,
              onNavigate: this.handleNavigate,
              onDrillDown: this.handleDrillDown,
              onSelectEvent: this.handleSelectEvent,
              onDoubleClickEvent: this.handleDoubleClickEvent,
              onKeyPressEvent: this.handleKeyPressEvent,
              onSelectSlot: this.handleSelectSlot,
              onShowMore: onShowMore,
            })
          )
        )
      }
      /**
       *
       * @param date
       * @param viewComponent
       * @param {'month'|'week'|'work_week'|'day'|'agenda'} [view] - optional
       * parameter. It appears when range change on view changing. It could be handy
       * when you need to have both: range and view type at once, i.e. for manage rbc
       * state via url
       */

      return Calendar
    })(React__default.Component)

  Calendar.defaultProps = {
    elementProps: {},
    popup: false,
    toolbar: true,
    view: views.MONTH,
    views: [views.MONTH, views.WEEK, views.DAY, views.AGENDA],
    step: 30,
    length: 30,
    drilldownView: views.DAY,
    titleAccessor: 'title',
    tooltipAccessor: 'title',
    allDayAccessor: 'allDay',
    startAccessor: 'start',
    endAccessor: 'end',
    resourceAccessor: 'resourceId',
    resourceIdAccessor: 'id',
    resourceTitleAccessor: 'title',
    longPressThreshold: 250,
    getNow: function getNow() {
      return new Date()
    },
    dayLayoutAlgorithm: 'overlap',
  }
  Calendar.propTypes = {
    localizer: propTypes.object.isRequired,

    /**
     * Props passed to main calendar `<div>`.
     *
     */
    elementProps: propTypes.object,

    /**
     * The current date value of the calendar. Determines the visible view range.
     * If `date` is omitted then the result of `getNow` is used; otherwise the
     * current date is used.
     *
     * @controllable onNavigate
     */
    date: propTypes.instanceOf(Date),

    /**
     * The current view of the calendar.
     *
     * @default 'month'
     * @controllable onView
     */
    view: propTypes.string,

    /**
     * The initial view set for the Calendar.
     * @type Calendar.Views ('month'|'week'|'work_week'|'day'|'agenda')
     * @default 'month'
     */
    defaultView: propTypes.string,

    /**
     * An array of event objects to display on the calendar. Events objects
     * can be any shape, as long as the Calendar knows how to retrieve the
     * following details of the event:
     *
     *  - start time
     *  - end time
     *  - title
     *  - whether its an "all day" event or not
     *  - any resource the event may be related to
     *
     * Each of these properties can be customized or generated dynamically by
     * setting the various "accessor" props. Without any configuration the default
     * event should look like:
     *
     * ```js
     * Event {
     *   title: string,
     *   start: Date,
     *   end: Date,
     *   allDay?: boolean
     *   resource?: any,
     * }
     * ```
     */
    events: propTypes.arrayOf(propTypes.object),

    /**
     * An array of background event objects to display on the calendar. Background
     * Events behave similarly to Events but are not factored into Event overlap logic,
     * allowing them to sit behind any Events that may occur during the same period.
     * Background Events objects can be any shape, as long as the Calendar knows how to
     * retrieve the following details of the event:
     *
     *  - start time
     *  - end time
     *
     * Each of these properties can be customized or generated dynamically by
     * setting the various "accessor" props. Without any configuration the default
     * event should look like:
     *
     * ```js
     * BackgroundEvent {
     *   start: Date,
     *   end: Date,
     * }
     * ```
     */
    backgroundEvents: propTypes.arrayOf(propTypes.object),

    /**
     * Accessor for the event title, used to display event information. Should
     * resolve to a `renderable` value.
     *
     * ```js
     * string | (event: Object) => string
     * ```
     *
     * @type {(func|string)}
     */
    titleAccessor: accessor,

    /**
     * Accessor for the event tooltip. Should
     * resolve to a `renderable` value. Removes the tooltip if null.
     *
     * ```js
     * string | (event: Object) => string
     * ```
     *
     * @type {(func|string)}
     */
    tooltipAccessor: accessor,

    /**
     * Determines whether the event should be considered an "all day" event and ignore time.
     * Must resolve to a `boolean` value.
     *
     * ```js
     * string | (event: Object) => boolean
     * ```
     *
     * @type {(func|string)}
     */
    allDayAccessor: accessor,

    /**
     * The start date/time of the event. Must resolve to a JavaScript `Date` object.
     *
     * ```js
     * string | (event: Object) => Date
     * ```
     *
     * @type {(func|string)}
     */
    startAccessor: accessor,

    /**
     * The end date/time of the event. Must resolve to a JavaScript `Date` object.
     *
     * ```js
     * string | (event: Object) => Date
     * ```
     *
     * @type {(func|string)}
     */
    endAccessor: accessor,

    /**
     * Returns the id of the `resource` that the event is a member of. This
     * id should match at least one resource in the `resources` array.
     *
     * ```js
     * string | (event: Object) => Date
     * ```
     *
     * @type {(func|string)}
     */
    resourceAccessor: accessor,

    /**
     * An array of resource objects that map events to a specific resource.
     * Resource objects, like events, can be any shape or have any properties,
     * but should be uniquly identifiable via the `resourceIdAccessor`, as
     * well as a "title" or name as provided by the `resourceTitleAccessor` prop.
     */
    resources: propTypes.arrayOf(propTypes.object),

    /**
     * Provides a unique identifier for each resource in the `resources` array
     *
     * ```js
     * string | (resource: Object) => any
     * ```
     *
     * @type {(func|string)}
     */
    resourceIdAccessor: accessor,

    /**
     * Provides a human readable name for the resource object, used in headers.
     *
     * ```js
     * string | (resource: Object) => any
     * ```
     *
     * @type {(func|string)}
     */
    resourceTitleAccessor: accessor,

    /**
     * Determines the current date/time which is highlighted in the views.
     *
     * The value affects which day is shaded and which time is shown as
     * the current time. It also affects the date used by the Today button in
     * the toolbar.
     *
     * Providing a value here can be useful when you are implementing time zones
     * using the `startAccessor` and `endAccessor` properties.
     *
     * @type {func}
     * @default () => new Date()
     */
    getNow: propTypes.func,

    /**
     * Callback fired when the `date` value changes.
     *
     * @controllable date
     */
    onNavigate: propTypes.func,

    /**
     * Callback fired when the `view` value changes.
     *
     * @controllable view
     */
    onView: propTypes.func,

    /**
     * Callback fired when date header, or the truncated events links are clicked
     *
     */
    onDrillDown: propTypes.func,

    /**
     *
     * ```js
     * (dates: Date[] | { start: Date; end: Date }, view: 'month'|'week'|'work_week'|'day'|'agenda'|undefined) => void
     * ```
     *
     * Callback fired when the visible date range changes. Returns an Array of dates
     * or an object with start and end dates for BUILTIN views. Optionally new `view`
     * will be returned when callback called after view change.
     *
     * Custom views may return something different.
     */
    onRangeChange: propTypes.func,

    /**
     * A callback fired when a date selection is made. Only fires when `selectable` is `true`.
     *
     * ```js
     * (
     *   slotInfo: {
     *     start: Date,
     *     end: Date,
     *     resourceId:  (number|string),
     *     slots: Array<Date>,
     *     action: "select" | "click" | "doubleClick",
     *     bounds: ?{ // For "select" action
     *       x: number,
     *       y: number,
     *       top: number,
     *       right: number,
     *       left: number,
     *       bottom: number,
     *     },
     *     box: ?{ // For "click" or "doubleClick" actions
     *       clientX: number,
     *       clientY: number,
     *       x: number,
     *       y: number,
     *     },
     *   }
     * ) => any
     * ```
     */
    onSelectSlot: propTypes.func,

    /**
     * Callback fired when a calendar event is selected.
     *
     * ```js
     * (event: Object, e: SyntheticEvent) => any
     * ```
     *
     * @controllable selected
     */
    onSelectEvent: propTypes.func,

    /**
     * Callback fired when a calendar event is clicked twice.
     *
     * ```js
     * (event: Object, e: SyntheticEvent) => void
     * ```
     */
    onDoubleClickEvent: propTypes.func,

    /**
     * Callback fired when a focused calendar event recieves a key press.
     *
     * ```js
     * (event: Object, e: SyntheticEvent) => void
     * ```
     */
    onKeyPressEvent: propTypes.func,

    /**
     * Callback fired when dragging a selection in the Time views.
     *
     * Returning `false` from the handler will prevent a selection.
     *
     * ```js
     * (range: { start: Date, end: Date, resourceId: (number|string) }) => ?boolean
     * ```
     */
    onSelecting: propTypes.func,

    /**
     * Callback fired when a +{count} more is clicked
     *
     * ```js
     * (events: Object, date: Date) => any
     * ```
     */
    onShowMore: propTypes.func,

    /**
     * Displays all events on the month view instead of
     * having some hidden behind +{count} more. This will
     * cause the rows in the month view to be scrollable if
     * the number of events exceed the height of the row.
     */
    showAllEvents: propTypes.bool,

    /**
     * The selected event, if any.
     */
    selected: propTypes.object,

    /**
     * An array of built-in view names to allow the calendar to display.
     * accepts either an array of builtin view names,
     *
     * ```jsx
     * views={['month', 'day', 'agenda']}
     * ```
     * or an object hash of the view name and the component (or boolean for builtin).
     *
     * ```jsx
     * views={{
     *   month: true,
     *   week: false,
     *   myweek: WorkWeekViewComponent,
     * }}
     * ```
     *
     * Custom views can be any React component, that implements the following
     * interface:
     *
     * ```js
     * interface View {
     *   static title(date: Date, { formats: DateFormat[], culture: string?, ...props }): string
     *   static navigate(date: Date, action: 'PREV' | 'NEXT' | 'DATE'): Date
     * }
     * ```
     *
     * @type Views ('month'|'week'|'work_week'|'day'|'agenda')
     * @View
     ['month', 'week', 'day', 'agenda']
     */
    views: views$1,

    /**
     * The string name of the destination view for drill-down actions, such
     * as clicking a date header, or the truncated events links. If
     * `getDrilldownView` is also specified it will be used instead.
     *
     * Set to `null` to disable drill-down actions.
     *
     * ```js
     * <Calendar
     *   drilldownView="agenda"
     * />
     * ```
     */
    drilldownView: propTypes.string,

    /**
     * Functionally equivalent to `drilldownView`, but accepts a function
     * that can return a view name. It's useful for customizing the drill-down
     * actions depending on the target date and triggering view.
     *
     * Return `null` to disable drill-down actions.
     *
     * ```js
     * <Calendar
     *   getDrilldownView={(targetDate, currentViewName, configuredViewNames) =>
     *     if (currentViewName === 'month' && configuredViewNames.includes('week'))
     *       return 'week'
     *
     *     return null;
     *   }}
     * />
     * ```
     */
    getDrilldownView: propTypes.func,

    /**
     * Determines the end date from date prop in the agenda view
     * date prop + length (in number of days) = end date
     */
    length: propTypes.number,

    /**
     * Determines whether the toolbar is displayed
     */
    toolbar: propTypes.bool,

    /**
     * Show truncated events in an overlay when you click the "+_x_ more" link.
     */
    popup: propTypes.bool,

    /**
     * Distance in pixels, from the edges of the viewport, the "show more" overlay should be positioned.
     *
     * ```jsx
     * <Calendar popupOffset={30}/>
     * <Calendar popupOffset={{x: 30, y: 20}}/>
     * ```
     */
    popupOffset: propTypes.oneOfType([
      propTypes.number,
      propTypes.shape({
        x: propTypes.number,
        y: propTypes.number,
      }),
    ]),

    /**
     * Allows mouse selection of ranges of dates/times.
     *
     * The 'ignoreEvents' option prevents selection code from running when a
     * drag begins over an event. Useful when you want custom event click or drag
     * logic
     */
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),

    /**
     * Specifies the number of miliseconds the user must press and hold on the screen for a touch
     * to be considered a "long press." Long presses are used for time slot selection on touch
     * devices.
     *
     * @type {number}
     * @default 250
     */
    longPressThreshold: propTypes.number,

    /**
     * Determines the selectable time increments in week and day views, in minutes.
     */
    step: propTypes.number,

    /**
     * The number of slots per "section" in the time grid views. Adjust with `step`
     * to change the default of 1 hour long groups, with 30 minute slots.
     */
    timeslots: propTypes.number,

    /**
     *Switch the calendar to a `right-to-left` read direction.
     */
    rtl: propTypes.bool,

    /**
     * Optionally provide a function that returns an object of className or style props
     * to be applied to the the event node.
     *
     * ```js
     * (
     * 	event: Object,
     * 	start: Date,
     * 	end: Date,
     * 	isSelected: boolean
     * ) => { className?: string, style?: Object }
     * ```
     */
    eventPropGetter: propTypes.func,

    /**
     * Optionally provide a function that returns an object of className or style props
     * to be applied to the time-slot node. Caution! Styles that change layout or
     * position may break the calendar in unexpected ways.
     *
     * ```js
     * (date: Date, resourceId: (number|string)) => { className?: string, style?: Object }
     * ```
     */
    slotPropGetter: propTypes.func,

    /**
     * Optionally provide a function that returns an object of props to be applied
     * to the time-slot group node. Useful to dynamically change the sizing of time nodes.
     * ```js
     * () => { style?: Object }
     * ```
     */
    slotGroupPropGetter: propTypes.func,

    /**
     * Optionally provide a function that returns an object of className or style props
     * to be applied to the the day background. Caution! Styles that change layout or
     * position may break the calendar in unexpected ways.
     *
     * ```js
     * (date: Date) => { className?: string, style?: Object }
     * ```
     */
    dayPropGetter: propTypes.func,

    /**
     * Support to show multi-day events with specific start and end times in the
     * main time grid (rather than in the all day header).
     *
     * **Note: This may cause calendars with several events to look very busy in
     * the week and day views.**
     */
    showMultiDayTimes: propTypes.bool,

    /**
     * Constrains the minimum _time_ of the Day and Week views.
     */
    min: propTypes.instanceOf(Date),

    /**
     * Constrains the maximum _time_ of the Day and Week views.
     */
    max: propTypes.instanceOf(Date),

    /**
     * Determines how far down the scroll pane is initially scrolled down.
     */
    scrollToTime: propTypes.instanceOf(Date),

    /**
     * Specify a specific culture code for the Calendar.
     *
     * **Note: it's generally better to handle this globally via your i18n library.**
     */
    culture: propTypes.string,

    /**
     * Localizer specific formats, tell the Calendar how to format and display dates.
     *
     * `format` types are dependent on the configured localizer; both Moment and Globalize
     * accept strings of tokens according to their own specification, such as: `'DD mm yyyy'`.
     *
     * ```jsx
     * let formats = {
     *   dateFormat: 'dd',
     *
     *   dayFormat: (date, , localizer) =>
     *     localizer.format(date, 'DDD', culture),
     *
     *   dayRangeHeaderFormat: ({ start, end }, culture, localizer) =>
     *     localizer.format(start, { date: 'short' }, culture) + ' – ' +
     *     localizer.format(end, { date: 'short' }, culture)
     * }
     *
     * <Calendar formats={formats} />
     * ```
     *
     * All localizers accept a function of
     * the form `(date: Date, culture: ?string, localizer: Localizer) -> string`
     */
    formats: propTypes.shape({
      /**
       * Format for the day of the month heading in the Month view.
       * e.g. "01", "02", "03", etc
       */
      dateFormat: dateFormat,

      /**
       * A day of the week format for Week and Day headings,
       * e.g. "Wed 01/04"
       *
       */
      dayFormat: dateFormat,

      /**
       * Week day name format for the Month week day headings,
       * e.g: "Sun", "Mon", "Tue", etc
       *
       */
      weekdayFormat: dateFormat,

      /**
       * The timestamp cell formats in Week and Time views, e.g. "4:00 AM"
       */
      timeGutterFormat: dateFormat,

      /**
       * Toolbar header format for the Month view, e.g "2015 April"
       *
       */
      monthHeaderFormat: dateFormat,

      /**
       * Toolbar header format for the Week views, e.g. "Mar 29 - Apr 04"
       */
      dayRangeHeaderFormat: dateRangeFormat,

      /**
       * Toolbar header format for the Day view, e.g. "Wednesday Apr 01"
       */
      dayHeaderFormat: dateFormat,

      /**
       * Toolbar header format for the Agenda view, e.g. "4/1/2015 – 5/1/2015"
       */
      agendaHeaderFormat: dateRangeFormat,

      /**
       * A time range format for selecting time slots, e.g "8:00am – 2:00pm"
       */
      selectRangeFormat: dateRangeFormat,
      agendaDateFormat: dateFormat,
      agendaTimeFormat: dateFormat,
      agendaTimeRangeFormat: dateRangeFormat,

      /**
       * Time range displayed on events.
       */
      eventTimeRangeFormat: dateRangeFormat,

      /**
       * An optional event time range for events that continue onto another day
       */
      eventTimeRangeStartFormat: dateFormat,

      /**
       * An optional event time range for events that continue from another day
       */
      eventTimeRangeEndFormat: dateFormat,
    }),

    /**
     * Customize how different sections of the calendar render by providing custom Components.
     * In particular the `Event` component can be specified for the entire calendar, or you can
     * provide an individual component for each view type.
     *
     * ```jsx
     * let components = {
     *   event: MyEvent, // used by each view (Month, Day, Week)
     *   eventWrapper: MyEventWrapper,
     *   eventContainerWrapper: MyEventContainerWrapper,
     *   dateCellWrapper: MyDateCellWrapper,
     *   timeSlotWrapper: MyTimeSlotWrapper,
     *   timeGutterHeader: MyTimeGutterWrapper,
     *   toolbar: MyToolbar,
     *   agenda: {
     *   	 event: MyAgendaEvent // with the agenda view use a different component to render events
     *     time: MyAgendaTime,
     *     date: MyAgendaDate,
     *   },
     *   day: {
     *     header: MyDayHeader,
     *     event: MyDayEvent,
     *   },
     *   week: {
     *     header: MyWeekHeader,
     *     event: MyWeekEvent,
     *   },
     *   month: {
     *     header: MyMonthHeader,
     *     dateHeader: MyMonthDateHeader,
     *     event: MyMonthEvent,
     *   }
     * }
     * <Calendar components={components} />
     * ```
     */
    components: propTypes.shape({
      event: propTypes.elementType,
      eventWrapper: propTypes.elementType,
      eventContainerWrapper: propTypes.elementType,
      dateCellWrapper: propTypes.elementType,
      timeSlotWrapper: propTypes.elementType,
      timeGutterHeader: propTypes.elementType,
      resourceHeader: propTypes.elementType,
      toolbar: propTypes.elementType,
      agenda: propTypes.shape({
        date: propTypes.elementType,
        time: propTypes.elementType,
        event: propTypes.elementType,
      }),
      day: propTypes.shape({
        header: propTypes.elementType,
        event: propTypes.elementType,
      }),
      week: propTypes.shape({
        header: propTypes.elementType,
        event: propTypes.elementType,
      }),
      month: propTypes.shape({
        header: propTypes.elementType,
        dateHeader: propTypes.elementType,
        event: propTypes.elementType,
      }),
    }),

    /**
     * String messages used throughout the component, override to provide localizations
     */
    messages: propTypes.shape({
      allDay: propTypes.node,
      previous: propTypes.node,
      next: propTypes.node,
      today: propTypes.node,
      month: propTypes.node,
      week: propTypes.node,
      day: propTypes.node,
      agenda: propTypes.node,
      date: propTypes.node,
      time: propTypes.node,
      event: propTypes.node,
      noEventsInRange: propTypes.node,
      showMore: propTypes.func,
    }),

    /**
     * A day event layout(arrangement) algorithm.
     * `overlap` allows events to be overlapped.
     * `no-overlap` resizes events to avoid overlap.
     * or custom `Function(events, minimumStartDifference, slotMetrics, accessors)`
     */
    dayLayoutAlgorithm: DayLayoutAlgorithmPropType,
  }
  var Calendar$1 = uncontrollable(Calendar, {
    view: 'onView',
    date: 'onNavigate',
    selected: 'onSelectEvent',
  })

  var dateRangeFormat$1 = function dateRangeFormat(_ref, culture, local) {
    var start = _ref.start,
      end = _ref.end
    return (
      local.format(start, 'L', culture) +
      ' – ' +
      local.format(end, 'L', culture)
    )
  }

  var timeRangeFormat = function timeRangeFormat(_ref2, culture, local) {
    var start = _ref2.start,
      end = _ref2.end
    return (
      local.format(start, 'LT', culture) +
      ' – ' +
      local.format(end, 'LT', culture)
    )
  }

  var timeRangeStartFormat = function timeRangeStartFormat(
    _ref3,
    culture,
    local
  ) {
    var start = _ref3.start
    return local.format(start, 'LT', culture) + ' – '
  }

  var timeRangeEndFormat = function timeRangeEndFormat(_ref4, culture, local) {
    var end = _ref4.end
    return ' – ' + local.format(end, 'LT', culture)
  }

  var weekRangeFormat = function weekRangeFormat(_ref5, culture, local) {
    var start = _ref5.start,
      end = _ref5.end
    return (
      local.format(start, 'MMMM DD', culture) +
      ' – ' +
      local.format(end, eq(start, end, 'month') ? 'DD' : 'MMMM DD', culture)
    )
  }

  var formats = {
    dateFormat: 'DD',
    dayFormat: 'DD ddd',
    weekdayFormat: 'ddd',
    selectRangeFormat: timeRangeFormat,
    eventTimeRangeFormat: timeRangeFormat,
    eventTimeRangeStartFormat: timeRangeStartFormat,
    eventTimeRangeEndFormat: timeRangeEndFormat,
    timeGutterFormat: 'LT',
    monthHeaderFormat: 'MMMM YYYY',
    dayHeaderFormat: 'dddd MMM DD',
    dayRangeHeaderFormat: weekRangeFormat,
    agendaHeaderFormat: dateRangeFormat$1,
    agendaDateFormat: 'ddd MMM DD',
    agendaTimeFormat: 'LT',
    agendaTimeRangeFormat: timeRangeFormat,
  }
  function moment(moment) {
    var locale = function locale(m, c) {
      return c ? m.locale(c) : m
    }

    return new DateLocalizer({
      formats: formats,
      firstOfWeek: function firstOfWeek(culture) {
        var data = culture ? moment.localeData(culture) : moment.localeData()
        return data ? data.firstDayOfWeek() : 0
      },
      format: function format(value, _format, culture) {
        return locale(moment(value), culture).format(_format)
      },
    })
  }

  var dateRangeFormat$2 = function dateRangeFormat(_ref, culture, local) {
    var start = _ref.start,
      end = _ref.end
    return (
      local.format(start, 'd', culture) +
      ' – ' +
      local.format(end, 'd', culture)
    )
  }

  var timeRangeFormat$1 = function timeRangeFormat(_ref2, culture, local) {
    var start = _ref2.start,
      end = _ref2.end
    return (
      local.format(start, 't', culture) +
      ' – ' +
      local.format(end, 't', culture)
    )
  }

  var timeRangeStartFormat$1 = function timeRangeStartFormat(
    _ref3,
    culture,
    local
  ) {
    var start = _ref3.start
    return local.format(start, 't', culture) + ' – '
  }

  var timeRangeEndFormat$1 = function timeRangeEndFormat(
    _ref4,
    culture,
    local
  ) {
    var end = _ref4.end
    return ' – ' + local.format(end, 't', culture)
  }

  var weekRangeFormat$1 = function weekRangeFormat(_ref5, culture, local) {
    var start = _ref5.start,
      end = _ref5.end
    return (
      local.format(start, 'MMM dd', culture) +
      ' – ' +
      local.format(end, eq(start, end, 'month') ? 'dd' : 'MMM dd', culture)
    )
  }

  var formats$1 = {
    dateFormat: 'dd',
    dayFormat: 'ddd dd/MM',
    weekdayFormat: 'ddd',
    selectRangeFormat: timeRangeFormat$1,
    eventTimeRangeFormat: timeRangeFormat$1,
    eventTimeRangeStartFormat: timeRangeStartFormat$1,
    eventTimeRangeEndFormat: timeRangeEndFormat$1,
    timeGutterFormat: 't',
    monthHeaderFormat: 'Y',
    dayHeaderFormat: 'dddd MMM dd',
    dayRangeHeaderFormat: weekRangeFormat$1,
    agendaHeaderFormat: dateRangeFormat$2,
    agendaDateFormat: 'ddd MMM dd',
    agendaTimeFormat: 't',
    agendaTimeRangeFormat: timeRangeFormat$1,
  }
  function oldGlobalize(globalize) {
    function getCulture(culture) {
      return culture
        ? globalize.findClosestCulture(culture)
        : globalize.culture()
    }

    function firstOfWeek(culture) {
      culture = getCulture(culture)
      return (culture && culture.calendar.firstDay) || 0
    }

    return new DateLocalizer({
      firstOfWeek: firstOfWeek,
      formats: formats$1,
      format: function format(value, _format, culture) {
        return globalize.format(value, _format, culture)
      },
    })
  }

  var dateRangeFormat$3 = function dateRangeFormat(_ref, culture, local) {
    var start = _ref.start,
      end = _ref.end
    return (
      local.format(
        start,
        {
          date: 'short',
        },
        culture
      ) +
      ' – ' +
      local.format(
        end,
        {
          date: 'short',
        },
        culture
      )
    )
  }

  var timeRangeFormat$2 = function timeRangeFormat(_ref2, culture, local) {
    var start = _ref2.start,
      end = _ref2.end
    return (
      local.format(
        start,
        {
          time: 'short',
        },
        culture
      ) +
      ' – ' +
      local.format(
        end,
        {
          time: 'short',
        },
        culture
      )
    )
  }

  var timeRangeStartFormat$2 = function timeRangeStartFormat(
    _ref3,
    culture,
    local
  ) {
    var start = _ref3.start
    return (
      local.format(
        start,
        {
          time: 'short',
        },
        culture
      ) + ' – '
    )
  }

  var timeRangeEndFormat$2 = function timeRangeEndFormat(
    _ref4,
    culture,
    local
  ) {
    var end = _ref4.end
    return (
      ' – ' +
      local.format(
        end,
        {
          time: 'short',
        },
        culture
      )
    )
  }

  var weekRangeFormat$2 = function weekRangeFormat(_ref5, culture, local) {
    var start = _ref5.start,
      end = _ref5.end
    return (
      local.format(start, 'MMM dd', culture) +
      ' – ' +
      local.format(end, eq(start, end, 'month') ? 'dd' : 'MMM dd', culture)
    )
  }

  var formats$2 = {
    dateFormat: 'dd',
    dayFormat: 'eee dd/MM',
    weekdayFormat: 'eee',
    selectRangeFormat: timeRangeFormat$2,
    eventTimeRangeFormat: timeRangeFormat$2,
    eventTimeRangeStartFormat: timeRangeStartFormat$2,
    eventTimeRangeEndFormat: timeRangeEndFormat$2,
    timeGutterFormat: {
      time: 'short',
    },
    monthHeaderFormat: 'MMMM yyyy',
    dayHeaderFormat: 'eeee MMM dd',
    dayRangeHeaderFormat: weekRangeFormat$2,
    agendaHeaderFormat: dateRangeFormat$3,
    agendaDateFormat: 'eee MMM dd',
    agendaTimeFormat: {
      time: 'short',
    },
    agendaTimeRangeFormat: timeRangeFormat$2,
  }
  function globalize(globalize) {
    var locale = function locale(culture) {
      return culture ? globalize(culture) : globalize
    } // return the first day of the week from the locale data. Defaults to 'world'
    // territory if no territory is derivable from CLDR.
    // Failing to use CLDR supplemental (not loaded?), revert to the original
    // method of getting first day of week.

    function firstOfWeek(culture) {
      try {
        var days = ['sun', 'mon', 'tue', 'wed', 'thu', 'fri', 'sat']
        var cldr = locale(culture).cldr
        var territory = cldr.attributes.territory
        var weekData = cldr.get('supplemental').weekData
        var firstDay = weekData.firstDay[territory || '001']
        return days.indexOf(firstDay)
      } catch (e) {
        {
          console.error(
            'Failed to accurately determine first day of the week.' +
              ' Is supplemental data loaded into CLDR?'
          )
        } // maybe cldr supplemental is not loaded? revert to original method

        var date = new Date() //cldr-data doesn't seem to be zero based

        var localeDay = Math.max(
          parseInt(
            locale(culture).formatDate(date, {
              raw: 'e',
            }),
            10
          ) - 1,
          0
        )
        return Math.abs(date.getDay() - localeDay)
      }
    }

    if (!globalize.load) return oldGlobalize(globalize)
    return new DateLocalizer({
      firstOfWeek: firstOfWeek,
      formats: formats$2,
      format: function format(value, _format, culture) {
        _format =
          typeof _format === 'string'
            ? {
                raw: _format,
              }
            : _format
        return locale(culture).formatDate(value, _format)
      },
    })
  }

  var dateRangeFormat$4 = function dateRangeFormat(_ref, culture, local) {
    var start = _ref.start,
      end = _ref.end
    return (
      local.format(start, 'P', culture) +
      ' \u2013 ' +
      local.format(end, 'P', culture)
    )
  }

  var timeRangeFormat$3 = function timeRangeFormat(_ref2, culture, local) {
    var start = _ref2.start,
      end = _ref2.end
    return (
      local.format(start, 'p', culture) +
      ' \u2013 ' +
      local.format(end, 'p', culture)
    )
  }

  var timeRangeStartFormat$3 = function timeRangeStartFormat(
    _ref3,
    culture,
    local
  ) {
    var start = _ref3.start
    return local.format(start, 'h:mma', culture) + ' \u2013 '
  }

  var timeRangeEndFormat$3 = function timeRangeEndFormat(
    _ref4,
    culture,
    local
  ) {
    var end = _ref4.end
    return ' \u2013 ' + local.format(end, 'h:mma', culture)
  }

  var weekRangeFormat$3 = function weekRangeFormat(_ref5, culture, local) {
    var start = _ref5.start,
      end = _ref5.end
    return (
      local.format(start, 'MMMM dd', culture) +
      ' \u2013 ' +
      local.format(end, eq(start, end, 'month') ? 'dd' : 'MMMM dd', culture)
    )
  }

  var formats$3 = {
    dateFormat: 'dd',
    dayFormat: 'dd eee',
    weekdayFormat: 'cccc',
    selectRangeFormat: timeRangeFormat$3,
    eventTimeRangeFormat: timeRangeFormat$3,
    eventTimeRangeStartFormat: timeRangeStartFormat$3,
    eventTimeRangeEndFormat: timeRangeEndFormat$3,
    timeGutterFormat: 'p',
    monthHeaderFormat: 'MMMM yyyy',
    dayHeaderFormat: 'cccc MMM dd',
    dayRangeHeaderFormat: weekRangeFormat$3,
    agendaHeaderFormat: dateRangeFormat$4,
    agendaDateFormat: 'ccc MMM dd',
    agendaTimeFormat: 'p',
    agendaTimeRangeFormat: timeRangeFormat$3,
  }

  var dateFnsLocalizer = function dateFnsLocalizer(_ref6) {
    var startOfWeek = _ref6.startOfWeek,
      getDay = _ref6.getDay,
      _format = _ref6.format,
      locales = _ref6.locales
    return new DateLocalizer({
      formats: formats$3,
      firstOfWeek: function firstOfWeek(culture) {
        return getDay(
          startOfWeek(new Date(), {
            locale: locales[culture],
          })
        )
      },
      format: function format(value, formatString, culture) {
        return _format(new Date(value), formatString, {
          locale: locales[culture],
        })
      },
    })
  }

  var components = {
    eventWrapper: NoopWrapper,
    timeSlotWrapper: NoopWrapper,
    dateCellWrapper: NoopWrapper,
  }

  exports.Calendar = Calendar$1
  exports.DateLocalizer = DateLocalizer
  exports.Navigate = navigate
  exports.Views = views
  exports.components = components
  exports.dateFnsLocalizer = dateFnsLocalizer
  exports.globalizeLocalizer = globalize
  exports.momentLocalizer = moment
  exports.move = moveDate

  Object.defineProperty(exports, '__esModule', { value: true })
})
