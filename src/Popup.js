import PropTypes from 'prop-types'
import React from 'react'
import * as dates from './utils/dates'

import EventCell from './EventCell'
import { isSelected } from './utils/selection'

const Popup = ({
  events,
  selected,
  getters,
  accessors,
  components,
  onSelect,
  onDoubleClick,
  onKeyPress,
  slotStart,
  slotEnd,
  localizer,
}) => {
  if (!events) {
    return null
  }

  return (
    <div className="rbc-overlay">
      <div className="rbc-overlay-header">
        {localizer.format(slotStart, 'dayHeaderFormat')}
      </div>
      {events.map((event, idx) => (
        <EventCell
          key={idx}
          type="popup"
          event={event}
          getters={getters}
          onSelect={onSelect}
          accessors={accessors}
          components={components}
          onDoubleClick={onDoubleClick}
          onKeyPress={onKeyPress}
          continuesPrior={dates.lt(accessors.end(event), slotStart, 'day')}
          continuesAfter={dates.gte(accessors.start(event), slotEnd, 'day')}
          slotStart={slotStart}
          slotEnd={slotEnd}
          selected={isSelected(event, selected)}
          draggable={true}
          onDragStart={() => this.props.handleDragStart(event)}
          onDragEnd={() => this.props.show()}
        />
      ))}
    </div>
  )
}

Popup.propTypes = {
  events: PropTypes.array,
  selected: PropTypes.object,

  accessors: PropTypes.object.isRequired,
  components: PropTypes.object.isRequired,
  getters: PropTypes.object.isRequired,
  localizer: PropTypes.object.isRequired,
  onSelect: PropTypes.func,
  onDoubleClick: PropTypes.func,
  onKeyPress: PropTypes.func,
  handleDragStart: PropTypes.func,
  show: PropTypes.func,
  slotStart: PropTypes.instanceOf(Date),
  slotEnd: PropTypes.number,
}

export default Popup
