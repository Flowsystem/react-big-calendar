'use strict'

var _interopRequireDefault = require('@babel/runtime/helpers/interopRequireDefault')

var _interopRequireWildcard = require('@babel/runtime/helpers/interopRequireWildcard')

exports.__esModule = true
exports.default = void 0

var _propTypes = _interopRequireDefault(require('prop-types'))

var _react = _interopRequireDefault(require('react'))

var dates = _interopRequireWildcard(require('./utils/dates'))

var _EventCell = _interopRequireDefault(require('./EventCell'))

var _selection = require('./utils/selection')

var _this = void 0

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

  return _react.default.createElement(
    'div',
    {
      className: 'rbc-overlay',
    },
    _react.default.createElement(
      'div',
      {
        className: 'rbc-overlay-header',
      },
      localizer.format(slotStart, 'dayHeaderFormat')
    ),
    events.map(function(event, idx) {
      return _react.default.createElement(_EventCell.default, {
        key: idx,
        type: 'popup',
        event: event,
        getters: getters,
        onSelect: onSelect,
        accessors: accessors,
        components: components,
        onDoubleClick: onDoubleClick,
        onKeyPress: onKeyPress,
        continuesPrior: dates.lt(accessors.end(event), slotStart, 'day'),
        continuesAfter: dates.gte(accessors.start(event), slotEnd, 'day'),
        slotStart: slotStart,
        slotEnd: slotEnd,
        selected: (0, _selection.isSelected)(event, selected),
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

Popup.propTypes =
  process.env.NODE_ENV !== 'production'
    ? {
        events: _propTypes.default.array,
        selected: _propTypes.default.object,
        accessors: _propTypes.default.object.isRequired,
        components: _propTypes.default.object.isRequired,
        getters: _propTypes.default.object.isRequired,
        localizer: _propTypes.default.object.isRequired,
        onSelect: _propTypes.default.func,
        onDoubleClick: _propTypes.default.func,
        onKeyPress: _propTypes.default.func,
        handleDragStart: _propTypes.default.func,
        show: _propTypes.default.func,
        slotStart: _propTypes.default.instanceOf(Date),
        slotEnd: _propTypes.default.number,
      }
    : {}
var _default = Popup
exports.default = _default
module.exports = exports['default']
