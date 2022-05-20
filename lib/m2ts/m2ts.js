/**
 * mux.js
 *
 * Copyright (c) Brightcove
 * Licensed Apache-2.0 https://github.com/videojs/mux.js/blob/master/LICENSE
 *
 * A stream-based mp2t to mp4 converter. This utility can be used to
 * deliver mp4s to a SourceBuffer on platforms that support native
 * Media Source Extensions.
 */
'use strict';
var Stream = require('../utils/stream.js'),
  CaptionStream = require('./caption-stream'),
  StreamTypes = require('./stream-types'),
  TimestampRolloverStream = require('./timestamp-rollover-stream').TimestampRolloverStream;

// object types
var TransportPacketStream, KlvStream, TransportParseStream, ElementaryStream;

// constants
var
  MP2T_PACKET_LENGTH = 188, // bytes
  SYNC_BYTE = 0x47;

/**
 * Splits an incoming stream of binary data into MPEG-2 Transport
 * Stream packets.
 */
TransportPacketStream = function() {
  var
    buffer = new Uint8Array(MP2T_PACKET_LENGTH),
    bytesInBuffer = 0;

  TransportPacketStream.prototype.init.call(this);

   // Deliver new bytes to the stream.

  /**
   * Split a stream of data into M2TS packets
  **/
  this.push = function(bytes) {
    var
      startIndex = 0,
      endIndex = MP2T_PACKET_LENGTH,
      everything;

    // If there are bytes remaining from the last segment, prepend them to the
    // bytes that were pushed in
    if (bytesInBuffer) {
      everything = new Uint8Array(bytes.byteLength + bytesInBuffer);
      everything.set(buffer.subarray(0, bytesInBuffer));
      everything.set(bytes, bytesInBuffer);
      bytesInBuffer = 0;
    } else {
      everything = bytes;
    }

    // While we have enough data for a packet
    while (endIndex < everything.byteLength) {
      // Look for a pair of start and end sync bytes in the data..
      if (everything[startIndex] === SYNC_BYTE && everything[endIndex] === SYNC_BYTE) {
        // We found a packet so emit it and jump one whole packet forward in
        // the stream
        this.trigger('data', everything.subarray(startIndex, endIndex));
        startIndex += MP2T_PACKET_LENGTH;
        endIndex += MP2T_PACKET_LENGTH;
        continue;
      }
      // If we get here, we have somehow become de-synchronized and we need to step
      // forward one byte at a time until we find a pair of sync bytes that denote
      // a packet
      startIndex++;
      endIndex++;
    }

    // If there was some data left over at the end of the segment that couldn't
    // possibly be a whole packet, keep it because it might be the start of a packet
    // that continues in the next segment
    if (startIndex < everything.byteLength) {
      buffer.set(everything.subarray(startIndex), 0);
      bytesInBuffer = everything.byteLength - startIndex;
    }
  };

  /**
   * Passes identified M2TS packets to the TransportParseStream to be parsed
  **/
  this.flush = function() {
    // If the buffer contains a whole packet when we are being flushed, emit it
    // and empty the buffer. Otherwise hold onto the data because it may be
    // important for decoding the next segment
    if (bytesInBuffer === MP2T_PACKET_LENGTH && buffer[0] === SYNC_BYTE) {
      this.trigger('data', buffer);
      bytesInBuffer = 0;
    }
    this.trigger('done');
  };

  this.endTimeline = function() {
    this.flush();
    this.trigger('endedtimeline');
  };

  this.reset = function() {
    bytesInBuffer = 0;
    this.trigger('reset');
  };
};
TransportPacketStream.prototype = new Stream();

/**
 * This method parses KLV packets from MPEG-TS packets. It can handle a KLV packet contained within a single
 * MPEG-TS packet or spread out over multiple MPEG-TS packets so long as the packets are contiguous.
 */
KlvStream = function() {
  var klvPacketSize = 1,
      M2TS_PACKET_HEADER_SIZE = 4,
      KLV_HEADER = [0x06, 0x0E, 0x2B, 0x34, 0x02, 0x0B, 0x01, 0x01, 0x0E, 0x01, 0x03, 0x01, 0x01, 0x00, 0x00, 0x00],
      buffer = [],
      pts,
      self;

  TransportParseStream.prototype.init.call(this);
  self = this;

  this.push = function(packet) {
    if(buffer.length > 0) {
      const parsedTsPacket = this.parseM2TSPacket(packet);
      const parsedPesPacket = this.parsePESPacket(parsedTsPacket.payload);

      // Skip over the M2TS packet header and the adaptation field, if it is present, to get to the rest
      // of the KLV payload
      let offset = M2TS_PACKET_HEADER_SIZE + 1;
      if (parsedTsPacket.adaptationField && parsedTsPacket.adaptationField.adaptationFieldLength) {
        offset += parsedTsPacket.adaptationField.adaptationFieldLength;
      }

      const availablePayloadBytes = MP2T_PACKET_LENGTH - offset;

      let updatedBuffer = new Uint8Array(buffer.length + availablePayloadBytes);
      updatedBuffer.set(buffer);
      updatedBuffer.set(packet.subarray(offset, offset + availablePayloadBytes), buffer.length);
      buffer = updatedBuffer;
    } else {
      let index = this.indexOfSubArray(packet, KLV_HEADER);
      if(index >= 0) {
        pts = this.parsePtsFromTsPacket(packet);
        const parsedTsPacket = this.parseM2TSPacket(packet);
        const parsedPesPacket = this.parsePESPacket(parsedTsPacket.payload);
        buffer = packet.subarray(index);
        const berLengthFirstByte = buffer[KLV_HEADER.length];
        if (berLengthFirstByte >> 7) {
          // If the first bit is a 1 then we have a long-form BER
          const additionalBerBytes = berLengthFirstByte & 0x7F;
          const klvPayloadSize = this.parseLongFormBER(KLV_HEADER.length, additionalBerBytes, buffer);
          klvPacketSize = KLV_HEADER.length + 1 + additionalBerBytes + klvPayloadSize;
        } else {
          // Short form BER encoding
          klvPacketSize = KLV_HEADER.length + 1 + berLengthFirstByte;
        }
      }
    }

    if (buffer.length >= klvPacketSize) {
      buffer = buffer.subarray(0, klvPacketSize);
      this.trigger('data', { klv: buffer, pts: pts });
      buffer = [];
      klvPacketSize = 1;
    }
  };

  this.parseLongFormBER = function(bufferPtr, berLength, buffer) {
    let length = 0;
    for (let i = berLength; i > 0; i--) {
      length += buffer[bufferPtr + i] << (8 * (berLength - i));
    }
    return length;
  };

  this.indexOfSubArray = function(outerArray, subArray) {
    for(let i = 0; i < outerArray.length - subArray.length; i++) {
      for(let j = 0; j < subArray.length; j++) {
        if(outerArray[i+j] !== subArray[j]) {
          break;
        }
        if(j === subArray.length - 1) {
          return i;
        }
      }
    }
    return -1;
  };

  this.parsePtsFromTsPacket = function(m2tsPacket) {
    let offset = M2TS_PACKET_HEADER_SIZE;
    if (this.adaptationFieldPresent(m2tsPacket)) {
      offset += m2tsPacket[offset] + 1;
    }
    let pesPacket = m2tsPacket.subarray(offset);
    let ptsDtsFlags = pesPacket[7];
    let pts = 0;
    if (ptsDtsFlags & 0xC0) {
      pts = (pesPacket[9] & 0x0E) << 27 |
        (pesPacket[10] & 0xFF) << 20 |
        (pesPacket[11] & 0xFE) << 12 |
        (pesPacket[12] & 0xFF) <<  5 |
        (pesPacket[13] & 0xFE) >>>  3;
      pts *= 4; // Left shift by 2
      pts += (pesPacket[13] & 0x06) >>> 1; // OR by the two LSBs
    }
    return pts;
  }

  this.parseM2TSPacket = function(m2tsPacket) {
    const outputObject = {};
    if (m2tsPacket.length !== MP2T_PACKET_LENGTH) {
      // TS packet is malformed - return an empty object
      return outputObject;
    }

    outputObject.packetHeader = this.parseM2TSPacketHeader(m2tsPacket);
    outputObject.adaptationField = this.parseAdaptationField(outputObject.packetHeader, m2tsPacket);

    let payloadStartIndex = M2TS_PACKET_HEADER_SIZE;
    if(outputObject.packetHeader.adaptationFieldControl) {
      // The extra +1 is because the adaptation field length doesn't include the length byte itself
      payloadStartIndex += outputObject.adaptationField.adaptationFieldLength + 1;
    }

    // TODO: CP - I don't believe the indexOf check should be necessary, but it is with my test data.
    //  It checks to make sure we are not already at the PES packet header - if so, the PUSI flag is likely
    //  set incorrectly. To correct this, we continue parsing as if there is no PUSI value and the
    //  payload starts immediately. The payload is assumed to be the whole PES packet.
    if (outputObject.packetHeader.payloadUnitStartIndicator
      && this.indexOfSubArray(m2tsPacket, [0x00, 0x00, 0x01]) !== payloadStartIndex) {
      // Again, +1 because the payload pointer doesn't include itself (i.e. can be 0)
      payloadStartIndex += m2tsPacket[payloadStartIndex] + 1;
    }

    outputObject.payload = m2tsPacket.subarray(payloadStartIndex);

    return outputObject;
  };

  this.parseM2TSPacketHeader = function(m2tsPacket) {
    const outputObject = {};

    // bits 1-8 (sync byte)
    if (m2tsPacket[0] !== 0x47) {
      // Packet is malformed, return an empty object
      return outputObject;
    }

    // bit 9 (transport error indicator)
    outputObject.transportErrorIndicator = (m2tsPacket[1] & 0x80) >>> 7;

    // bit 10 (payload unit start indicator)
    outputObject.payloadUnitStartIndicator = (m2tsPacket[1] & 0x40) >>> 6;

    // bit 11 (transport priority)
    outputObject.transportPriority = (m2tsPacket[1] & 0x20) >>> 5;

    // bits 12-24 (PID)
    outputObject.pid = ((m2tsPacket[1] & 0x1F) << 8) + m2tsPacket[2];

    // bits 25-26 (transport scrambling control)
    outputObject.transportScramblingControl = (m2tsPacket[3] & 0xC0) >>> 6;

    // bits 27-28 (adaptation field control)
    outputObject.adaptationFieldControl = (m2tsPacket[3] & 0x30) >>> 4;

    // bits 29-32
    outputObject.continuityCounter = m2tsPacket[3] & 0x0F;

    return outputObject;
  };

  this.parseAdaptationField = function(m2tsHeader, m2tsPacket) {
    const outputObject = {};
    if(m2tsHeader.adaptationFieldControl <= 1) {
      return outputObject;
    }

    // bits 1-8 (adaptation field length)
    outputObject.adaptationFieldLength = m2tsPacket[4];

    // bit 9 (discontinuity indicator)
    outputObject.discontinuityIndicator = (m2tsPacket[5] & 0x80) >>> 7;

    // bit 10 (random access indicator)
    outputObject.randomAccessIndicator = (m2tsPacket[5] & 0x40) >>> 6;

    // bit 11 (elementary stream priority indicator)
    outputObject.elementaryStreamPriorityIndicator = (m2tsPacket[5] & 0x20) >>> 5;

    // bit 12 (program clock reference flag)
    outputObject.pcrFlag = (m2tsPacket[5] & 0x10) >>> 4;

    // bit 13 (original program clock reference flag)
    outputObject.opcrFlag = (m2tsPacket[5] & 0x08) >>> 3;

    // bit 14 (splicing point flag)
    outputObject.splicingPointFlag = (m2tsPacket[5] & 0x04) >>> 2;

    // bit 15 (transport private data flag)
    outputObject.transportPrivateDataFlag = (m2tsPacket[5] & 0x02) >>> 1;

    // bit 16 (adaptation field extension flag)
    outputObject.adaptationFieldExtensionFlag = m2tsPacket[5] & 0x01;

    // Optional fields
    let offset = 6;
    if (outputObject.pcrFlag) {
      outputObject.pcr = this.parsePcrValue(m2tsPacket, offset);
      offset += 6;
    }

    if (outputObject.opcrFlag) {
      outputObject.opcr = this.parsePcrValue(m2tsPacket, offset);
      offset += 6;
    }

    if (outputObject.splicingPointFlag) {
      outputObject.spliceCountdown = m2tsPacket[offset] & 0x7F;
      if ((m2tsPacket[offset] & 0x80) > 0) {
        outputObject.spliceCountdown = outputObject.spliceCountdown - 256;
      }
      offset += 1;
    }

    if (outputObject.transportPrivateDataFlag) {
      outputObject.transportPrivateDataLength = m2tsPacket[offset];
      offset += 1;
      outputObject.transportPrivateData = m2tsPacket.subarray(offset, offset + outputObject.transportPrivateDataLength);
      offset += outputObject.transportPrivateDataLength;
    }

    if (outputObject.adaptationFieldExtensionFlag) {
      // Don't parse this for now
      offset += 12;
    }

    outputObject.numStuffingBytes = 0;
    for (let i = offset; i < 6 + outputObject.adaptationFieldLength; i++) {
      if (m2tsPacket[i] === 0xFF) {
        outputObject.numStuffingBytes += 1;
      }
    }

    return outputObject;
  };

  this.parsePcrValue = function(m2tsPacket, offset) {
    // PCR = 33 bit base with a 90 kHz timescale + 6 reserved bits (ignored in calculation) + 9 extension bits
    // with a 2.7 MHz timescale. The PCR timescale is 2.7 MHz, so the base needs to be multiplied by 300 when
    // it is added to the extension.
    const base = (m2tsPacket[offset] << 25) + (m2tsPacket[offset + 1] << 17) + (m2tsPacket[offset + 2] << 9) +
      (m2tsPacket[offset + 3] << 1) + ((m2tsPacket[offset + 4] & 0x80) >> 7);
    const extension = ((m2tsPacket[offset + 4] & 0x01) << 8) + m2tsPacket[offset + 5];
    return base * 300 + extension;
  };

  this.adaptationFieldPresent = function(m2tsPacket) {
    return ((m2tsPacket[3] & 0x30) >>> 4) > 0x01;
  };

  this.parsePESPacket = function(pesPacket) {
    const outputObject = {};
    if (pesPacket.length < 3 || pesPacket[0] !== 0x00 || pesPacket[1] !== 0x00 || pesPacket[2] !== 0x01) {
      // Either the packet is too short, or the packet start code is not present
      return outputObject;
    }

    outputObject.streamId = pesPacket[3];
    outputObject.pesPacketLength = (pesPacket[4] << 8) + pesPacket[5];
    outputObject.pesHeader = this.parsePESHeader(pesPacket);

    outputObject.offsetToPayload = 6 + (outputObject.pesHeader.totalLength ? outputObject.pesHeader.totalLength : 0);

    return outputObject;
  };

  this.parsePESHeader = function(pesPacket) {
    const outputObject = {};

    // bits 1-2 (marker bits)
    outputObject.markerBits = (pesPacket[6] & 0xC0) >>> 6;

    // bits 3-4 (scrambling control)
    outputObject.scramblingControl = (pesPacket[6] & 0x30) >>> 4;

    // bit 5 (priority)
    outputObject.priority = (pesPacket[6] & 0x08) >>> 3;

    // bit 6 (data alignment indicator)
    outputObject.dataAlignmentIndicator = (pesPacket[6] & 0x04) >>> 2;

    // bit 7 (copyright)
    outputObject.copyright = (pesPacket[6] & 0x02) >>> 1;

    // bit 8 (original material)
    outputObject.original = pesPacket[6] & 0x01;

    // bits 9-10 (pts/dts indicator)
    outputObject.ptsDtsIndicator = (pesPacket[7] & 0xC0) >>> 6;

    // bit 11 (ESCR flag)
    outputObject.escrFlag = (pesPacket[7] & 0x20) >>> 5;

    // bit 12 (ES rate flag)
    outputObject.esRateFlag = (pesPacket[7] & 0x10) >>> 4;

    // bit 13 (DSM trick mode flag)
    outputObject.dsmTrickModeFlag = (pesPacket[7] & 0x08) >>> 3;

    // bit 14 (additional copy info flag)
    outputObject.additionalCopyInfoFlag = (pesPacket[7] & 0x04) >>> 2;

    // bit 15 (CRC flag)
    outputObject.crcFlag = (pesPacket[7] & 0x02) >>> 1;

    // bit 16 (extension flag)
    outputObject.extensionFlag = pesPacket[7] & 0x01;

    // bits 17-24 (PES header length)
    outputObject.pesHeaderLength = pesPacket[8];

    // Optional fields
    let offset = 9;
    if (outputObject.ptsDtsIndicator > 1) {
      // binary value of 10 or 11
      outputObject.pts = this.parsePtsDtsValue(pesPacket, offset);
      offset += 5;
      if (outputObject.ptsDtsIndicator > 2) {
        // binary value of 11
        outputObject.dts = this.parsePtsDtsValue(pesPacket, offset);
        offset += 5;
      }
    } else if (outputObject.ptsDtsIndicator === 1) {
      // Binary value of 01 is invalid - cannot only have DTS. Probably best to toss the whole packet in this case.
      return {};
    }

    outputObject.totalLength = offset;
    return outputObject;
  };

  this.parsePtsDtsValue = function(pesPacket, offset) {
    return ((pesPacket[offset] & 0x0E) << 29) +
      ((pesPacket[offset + 1] & 0xFF) << 22) +
      ((pesPacket[offset + 2] & 0xFE) << 14) +
      ((pesPacket[offset + 3] & 0xFF) << 7) +
      ((pesPacket[offset + 4] & 0xFE) >>> 1);
  };
};
KlvStream.prototype = new Stream();

/**
 * Accepts an MP2T TransportPacketStream and emits data events with parsed
 * forms of the individual transport stream packets.
 */
TransportParseStream = function() {
  var parsePsi, parsePat, parsePmt, self;
  TransportParseStream.prototype.init.call(this);
  self = this;

  this.packetsWaitingForPmt = [];
  this.programMapTable = undefined;

  parsePsi = function(payload, psi) {
    var offset = 0;

    // PSI packets may be split into multiple sections and those
    // sections may be split into multiple packets. If a PSI
    // section starts in this packet, the payload_unit_start_indicator
    // will be true and the first byte of the payload will indicate
    // the offset from the current position to the start of the
    // section.
    if (psi.payloadUnitStartIndicator) {
      offset += payload[offset] + 1;
    }

    if (psi.type === 'pat') {
      parsePat(payload.subarray(offset), psi);
    } else {
      parsePmt(payload.subarray(offset), psi);
    }
  };

  parsePat = function(payload, pat) {
    pat.section_number = payload[7]; // eslint-disable-line camelcase
    pat.last_section_number = payload[8]; // eslint-disable-line camelcase

    // skip the PSI header and parse the first PMT entry
    self.pmtPid = (payload[10] & 0x1F) << 8 | payload[11];
    pat.pmtPid = self.pmtPid;
  };

  /**
   * Parse out the relevant fields of a Program Map Table (PMT).
   * @param payload {Uint8Array} the PMT-specific portion of an MP2T
   * packet. The first byte in this array should be the table_id
   * field.
   * @param pmt {object} the object that should be decorated with
   * fields parsed from the PMT.
   */
  parsePmt = function(payload, pmt) {
    var sectionLength, tableEnd, programInfoLength, offset;

    // PMTs can be sent ahead of the time when they should actually
    // take effect. We don't believe this should ever be the case
    // for HLS but we'll ignore "forward" PMT declarations if we see
    // them. Future PMT declarations have the current_next_indicator
    // set to zero.
    if (!(payload[5] & 0x01)) {
      return;
    }

    // overwrite any existing program map table
    self.programMapTable = {
      video: null,
      audio: null,
      'timed-metadata': {}
    };

    // the mapping table ends at the end of the current section
    sectionLength = (payload[1] & 0x0f) << 8 | payload[2];
    tableEnd = 3 + sectionLength - 4;

    // to determine where the table is, we have to figure out how
    // long the program info descriptors are
    programInfoLength = (payload[10] & 0x0f) << 8 | payload[11];

    // advance the offset to the first entry in the mapping table
    offset = 12 + programInfoLength;
    while (offset < tableEnd) {
      var streamType = payload[offset];
      var pid = (payload[offset + 1] & 0x1F) << 8 | payload[offset + 2];

      // only map a single elementary_pid for audio and video stream types
      // TODO: should this be done for metadata too? for now maintain behavior of
      //       multiple metadata streams
      if (streamType === StreamTypes.H264_STREAM_TYPE &&
          self.programMapTable.video === null) {
        self.programMapTable.video = pid;
      } else if (streamType === StreamTypes.ADTS_STREAM_TYPE &&
                 self.programMapTable.audio === null) {
        self.programMapTable.audio = pid;
      } else if (streamType === StreamTypes.METADATA_STREAM_TYPE) {
        // map pid to stream type for metadata streams
        self.programMapTable['timed-metadata'][pid] = streamType;
      }

      // move to the next table entry
      // skip past the elementary stream descriptors, if present
      offset += ((payload[offset + 3] & 0x0F) << 8 | payload[offset + 4]) + 5;
    }

    // record the map on the packet as well
    pmt.programMapTable = self.programMapTable;
  };

  /**
   * Deliver a new MP2T packet to the next stream in the pipeline.
   */
  this.push = function(packet) {
    var
      result = {},
      offset = 4;

    result.payloadUnitStartIndicator = !!(packet[1] & 0x40);

    // pid is a 13-bit field starting at the last bit of packet[1]
    result.pid = packet[1] & 0x1f;
    result.pid <<= 8;
    result.pid |= packet[2];

    // if an adaption field is present, its length is specified by the
    // fifth byte of the TS packet header. The adaptation field is
    // used to add stuffing to PES packets that don't fill a complete
    // TS packet, and to specify some forms of timing and control data
    // that we do not currently use.
    if (((packet[3] & 0x30) >>> 4) > 0x01) {
      offset += packet[offset] + 1;
    }

    // parse the rest of the packet based on the type
    if (result.pid === 0) {
      result.type = 'pat';
      parsePsi(packet.subarray(offset), result);
      this.trigger('data', result);
    } else if (result.pid === this.pmtPid) {
      result.type = 'pmt';
      parsePsi(packet.subarray(offset), result);
      this.trigger('data', result);

      // if there are any packets waiting for a PMT to be found, process them now
      while (this.packetsWaitingForPmt.length) {
        this.processPes_.apply(this, this.packetsWaitingForPmt.shift());
      }
    } else if (this.programMapTable === undefined) {
      // When we have not seen a PMT yet, defer further processing of
      // PES packets until one has been parsed
      this.packetsWaitingForPmt.push([packet, offset, result]);
    } else {
      this.processPes_(packet, offset, result);
    }
  };

  this.processPes_ = function(packet, offset, result) {
    // set the appropriate stream type
    if (result.pid === this.programMapTable.video) {
      result.streamType = StreamTypes.H264_STREAM_TYPE;
    } else if (result.pid === this.programMapTable.audio) {
      result.streamType = StreamTypes.ADTS_STREAM_TYPE;
    } else {
      // if not video or audio, it is timed-metadata or unknown
      // if unknown, streamType will be undefined
      result.streamType = this.programMapTable['timed-metadata'][result.pid];
    }

    result.type = 'pes';
    result.data = packet.subarray(offset);
    this.trigger('data', result);
  };
};
TransportParseStream.prototype = new Stream();
TransportParseStream.STREAM_TYPES  = {
  h264: 0x1b,
  adts: 0x0f
};

/**
 * Reconsistutes program elementary stream (PES) packets from parsed
 * transport stream packets. That is, if you pipe an
 * mp2t.TransportParseStream into a mp2t.ElementaryStream, the output
 * events will be events which capture the bytes for individual PES
 * packets plus relevant metadata that has been extracted from the
 * container.
 */
ElementaryStream = function() {
  var
    self = this,
    segmentHadPmt = false,
    // PES packet fragments
    video = {
      data: [],
      size: 0
    },
    audio = {
      data: [],
      size: 0
    },
    timedMetadata = {
      data: [],
      size: 0
    },
    programMapTable,
    parsePes = function(payload, pes) {
      var ptsDtsFlags;
      const startPrefix = payload[0] << 16 | payload[1] << 8 | payload[2]
      // default to an empty array
      pes.data = new Uint8Array()
      // In certain live streams, the start of a TS fragment has ts packets
      // that are frame data that is continuing from the previous fragment. This
      // is to check that the pes data is the start of a new pes payload
      if (startPrefix !== 1) {
        return;
      }
      // get the packet length, this will be 0 for video
      pes.packetLength = 6 + ((payload[4] << 8) | payload[5]);

      // find out if this packets starts a new keyframe
      pes.dataAlignmentIndicator = (payload[6] & 0x04) !== 0;
      // PES packets may be annotated with a PTS value, or a PTS value
      // and a DTS value. Determine what combination of values is
      // available to work with.
      ptsDtsFlags = payload[7];

      // PTS and DTS are normally stored as a 33-bit number.  Javascript
      // performs all bitwise operations on 32-bit integers but javascript
      // supports a much greater range (52-bits) of integer using standard
      // mathematical operations.
      // We construct a 31-bit value using bitwise operators over the 31
      // most significant bits and then multiply by 4 (equal to a left-shift
      // of 2) before we add the final 2 least significant bits of the
      // timestamp (equal to an OR.)
      if (ptsDtsFlags & 0xC0) {
        // the PTS and DTS are not written out directly. For information
        // on how they are encoded, see
        // http://dvd.sourceforge.net/dvdinfo/pes-hdr.html
        pes.pts = (payload[9] & 0x0E) << 27 |
          (payload[10] & 0xFF) << 20 |
          (payload[11] & 0xFE) << 12 |
          (payload[12] & 0xFF) <<  5 |
          (payload[13] & 0xFE) >>>  3;
        pes.pts *= 4; // Left shift by 2
        pes.pts += (payload[13] & 0x06) >>> 1; // OR by the two LSBs
        pes.dts = pes.pts;
        if (ptsDtsFlags & 0x40) {
          pes.dts = (payload[14] & 0x0E) << 27 |
            (payload[15] & 0xFF) << 20 |
            (payload[16] & 0xFE) << 12 |
            (payload[17] & 0xFF) << 5 |
            (payload[18] & 0xFE) >>> 3;
          pes.dts *= 4; // Left shift by 2
          pes.dts += (payload[18] & 0x06) >>> 1; // OR by the two LSBs
        }
      }
      // the data section starts immediately after the PES header.
      // pes_header_data_length specifies the number of header bytes
      // that follow the last byte of the field.
      pes.data = payload.subarray(9 + payload[8]);
    },
    /**
      * Pass completely parsed PES packets to the next stream in the pipeline
     **/
    flushStream = function(stream, type, forceFlush) {
      var
        packetData = new Uint8Array(stream.size),
        event = {
          type: type
        },
        i = 0,
        offset = 0,
        packetFlushable = false,
        fragment;

      // do nothing if there is not enough buffered data for a complete
      // PES header
      if (!stream.data.length || stream.size < 9) {
        return;
      }
      event.trackId = stream.data[0].pid;

      // reassemble the packet
      for (i = 0; i < stream.data.length; i++) {
        fragment = stream.data[i];

        packetData.set(fragment.data, offset);
        offset += fragment.data.byteLength;
      }

      // parse assembled packet's PES header
      parsePes(packetData, event);

      // non-video PES packets MUST have a non-zero PES_packet_length
      // check that there is enough stream data to fill the packet
      packetFlushable = type === 'video' || event.packetLength <= stream.size;

      // flush pending packets if the conditions are right
      if (forceFlush || packetFlushable) {
        stream.size = 0;
        stream.data.length = 0;
      }

      // only emit packets that are complete. this is to avoid assembling
      // incomplete PES packets due to poor segmentation
      if (packetFlushable) {
        self.trigger('data', event);
      }
    };

  ElementaryStream.prototype.init.call(this);

  /**
   * Identifies M2TS packet types and parses PES packets using metadata
   * parsed from the PMT
   **/
  this.push = function(data) {
    ({
      pat: function() {
        // we have to wait for the PMT to arrive as well before we
        // have any meaningful metadata
      },
      pes: function() {
        var stream, streamType;

        switch (data.streamType) {
        case StreamTypes.H264_STREAM_TYPE:
          stream = video;
          streamType = 'video';
          break;
        case StreamTypes.ADTS_STREAM_TYPE:
          stream = audio;
          streamType = 'audio';
          break;
        case StreamTypes.METADATA_STREAM_TYPE:
          stream = timedMetadata;
          streamType = 'timed-metadata';
          break;
        default:
          // ignore unknown stream types
          return;
        }

        // if a new packet is starting, we can flush the completed
        // packet
        if (data.payloadUnitStartIndicator) {
          flushStream(stream, streamType, true);
        }

        // buffer this fragment until we are sure we've received the
        // complete payload
        stream.data.push(data);
        stream.size += data.data.byteLength;
      },
      pmt: function() {
        var
          event = {
            type: 'metadata',
            tracks: []
          };

        programMapTable = data.programMapTable;

        // translate audio and video streams to tracks
        if (programMapTable.video !== null) {
          event.tracks.push({
            timelineStartInfo: {
              baseMediaDecodeTime: 0
            },
            id: +programMapTable.video,
            codec: 'avc',
            type: 'video'
          });
        }
        if (programMapTable.audio !== null) {
          event.tracks.push({
            timelineStartInfo: {
              baseMediaDecodeTime: 0
            },
            id: +programMapTable.audio,
            codec: 'adts',
            type: 'audio'
          });
        }

        segmentHadPmt = true;

        self.trigger('data', event);
      }
    })[data.type]();
  };

  this.reset = function() {
    video.size = 0;
    video.data.length = 0;
    audio.size = 0;
    audio.data.length = 0;
    this.trigger('reset');
  };

  /**
   * Flush any remaining input. Video PES packets may be of variable
   * length. Normally, the start of a new video packet can trigger the
   * finalization of the previous packet. That is not possible if no
   * more video is forthcoming, however. In that case, some other
   * mechanism (like the end of the file) has to be employed. When it is
   * clear that no additional data is forthcoming, calling this method
   * will flush the buffered packets.
   */
  this.flushStreams_ = function() {
    // !!THIS ORDER IS IMPORTANT!!
    // video first then audio
    flushStream(video, 'video');
    flushStream(audio, 'audio');
    flushStream(timedMetadata, 'timed-metadata');
  };

  this.flush = function() {
    // if on flush we haven't had a pmt emitted
    // and we have a pmt to emit. emit the pmt
    // so that we trigger a trackinfo downstream.
    if (!segmentHadPmt && programMapTable) {
      var
        pmt = {
          type: 'metadata',
          tracks: []
        };
      // translate audio and video streams to tracks
      if (programMapTable.video !== null) {
        pmt.tracks.push({
          timelineStartInfo: {
            baseMediaDecodeTime: 0
          },
          id: +programMapTable.video,
          codec: 'avc',
          type: 'video'
        });
      }

      if (programMapTable.audio !== null) {
        pmt.tracks.push({
          timelineStartInfo: {
            baseMediaDecodeTime: 0
          },
          id: +programMapTable.audio,
          codec: 'adts',
          type: 'audio'
        });
      }

      self.trigger('data', pmt);
    }

    segmentHadPmt = false;
    this.flushStreams_();
    this.trigger('done');
  };
};
ElementaryStream.prototype = new Stream();

var m2ts = {
  PAT_PID: 0x0000,
  MP2T_PACKET_LENGTH: MP2T_PACKET_LENGTH,
  TransportPacketStream: TransportPacketStream,
  KlvStream: KlvStream,
  TransportParseStream: TransportParseStream,
  ElementaryStream: ElementaryStream,
  TimestampRolloverStream: TimestampRolloverStream,
  CaptionStream: CaptionStream.CaptionStream,
  Cea608Stream: CaptionStream.Cea608Stream,
  Cea708Stream: CaptionStream.Cea708Stream,
  MetadataStream: require('./metadata-stream')
};

for (var type in StreamTypes) {
  if (StreamTypes.hasOwnProperty(type)) {
    m2ts[type] = StreamTypes[type];
  }
}

module.exports = m2ts;
