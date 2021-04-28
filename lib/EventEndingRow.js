'use strict'

var _interopRequireDefault = require('@babel/runtime/helpers/interopRequireDefault')

exports.__esModule = true
exports.default = void 0

var _extends2 = _interopRequireDefault(
  require('@babel/runtime/helpers/extends')
)

var _inheritsLoose2 = _interopRequireDefault(
  require('@babel/runtime/helpers/inheritsLoose')
)

var _propTypes = _interopRequireDefault(require('prop-types'))

var _react = _interopRequireDefault(require('react'))

var _EventRowMixin = _interopRequireDefault(require('./EventRowMixin'))

var _eventLevels = require('./utils/eventLevels')

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
    ;(0, _inheritsLoose2.default)(EventEndingRow, _React$Component)

    function EventEndingRow() {
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

      _this.showMore = function(e, onShowMore, slot) {
        e.preventDefault()
        var getShowMoreInfo = _this.props.getShowMoreInfo

        var _getShowMoreInfo = getShowMoreInfo(slot),
          events = _getShowMoreInfo.events,
          slotRange = _getShowMoreInfo.slotRange,
          cell = _getShowMoreInfo.cell

        onShowMore(events, slotRange, cell, slot)
      }

      return _this
    }

    var _proto = EventEndingRow.prototype

    _proto.render = function render() {
      var _this$props = this.props,
        segments = _this$props.segments,
        slots = _this$props.slotMetrics.slots
      var rowSegments = (0, _eventLevels.eventLevels)(segments).levels[0]
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
          left = _ref.left //eslint-disable-line

        if (!event) {
          current++
          continue
        }

        var gap = Math.max(0, left - lastEnd)

        if (gap) {
          row.push(_EventRowMixin.default.renderSpan(slots, gap, key + '_gap'))
        }

        row.push(
          _EventRowMixin.default.renderSpan(
            slots,
            1,
            key,
            this.renderShowMore(segments, current)
          )
        )
        lastEnd = current = current + 1
      }

      return _react.default.createElement(
        'div',
        {
          className: 'rbc-row',
        },
        row
      )
    }

    _proto.renderShowMore = function renderShowMore(segments, slot) {
      var _this2 = this

      var _this$props2 = this.props,
        localizer = _this$props2.localizer,
        renderPopover = _this$props2.renderPopover,
        getShowMoreInfo = _this$props2.getShowMoreInfo
      var count = eventsInSlot(segments, slot)

      var _getShowMoreInfo2 = getShowMoreInfo(slot),
        cell = _getShowMoreInfo2.cell

      if (!count) {
        return false
      }

      return renderPopover(cell, function(_ref2) {
        var onShowMore = _ref2.onShowMore
        return _react.default.createElement(
          'a',
          {
            key: 'sm_' + slot,
            href: '#',
            className: 'rbc-show-more',
            onClick: function onClick(e) {
              _this2.showMore(e, onShowMore, slot)
            },
          },
          localizer.messages.showMore(count)
        )
      })
    }

    return EventEndingRow
  })(_react.default.Component)

EventEndingRow.propTypes =
  process.env.NODE_ENV !== 'production'
    ? (0, _extends2.default)(
        {
          segments: _propTypes.default.array,
          slots: _propTypes.default.number,
          getShowMoreInfo: _propTypes.default.func,
        },
        _EventRowMixin.default.propTypes
      )
    : {}
EventEndingRow.defaultProps = (0, _extends2.default)(
  {},
  _EventRowMixin.default.defaultProps
)
var _default = EventEndingRow
exports.default = _default
module.exports = exports['default']
