import PropTypes from 'prop-types'
import React from 'react'
import EventRowMixin from './EventRowMixin'
import { eventLevels } from './utils/eventLevels'

let isSegmentInSlot = (seg, slot) => seg.left <= slot && seg.right >= slot
let eventsInSlot = (segments, slot) =>
  segments.filter(seg => isSegmentInSlot(seg, slot)).length

class EventEndingRow extends React.Component {
  render() {
    let {
      segments,
      slotMetrics: { slots },
    } = this.props
    let rowSegments = eventLevels(segments).levels[0]

    let current = 1,
      lastEnd = 1,
      row = []

    while (current <= slots) {
      let key = '_lvl_' + current

      let { event, left } =
        rowSegments.filter(seg => isSegmentInSlot(seg, current))[0] || {} //eslint-disable-line

      if (!event) {
        current++
        continue
      }

      let gap = Math.max(0, left - lastEnd)

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

    return <div className="rbc-row">{row}</div>
  }

  renderShowMore(segments, slot) {
    let { localizer, renderPopover, getShowMoreInfo } = this.props
    let count = eventsInSlot(segments, slot)
    const { cell } = getShowMoreInfo(slot)

    if (!count) {
      return false
    }

    return renderPopover(cell, ({ onShowMore }) => (
      <a
        key={'sm_' + slot}
        href="#"
        className={'rbc-show-more'}
        onClick={e => {
          this.showMore(e, onShowMore, slot)
        }}
      >
        {localizer.messages.showMore(count)}
      </a>
    ))
  }

  showMore = (e, onShowMore, slot) => {
    e.preventDefault()
    const { getShowMoreInfo } = this.props

    const { events, slotRange, cell } = getShowMoreInfo(slot)

    onShowMore(events, slotRange, cell, slot)
  }
}

EventEndingRow.propTypes = {
  segments: PropTypes.array,
  slots: PropTypes.number,
  getShowMoreInfo: PropTypes.func,
  ...EventRowMixin.propTypes,
}

EventEndingRow.defaultProps = {
  ...EventRowMixin.defaultProps,
}

export default EventEndingRow
