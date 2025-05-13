module JoinMsg
{
  use ServerConfig;

  use Time;
  use Math only;
  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use SegmentedString;
  use ServerErrorStrings;
  use CommAggregation;
  use PrivateDist;
  
  use AryUtil;
  use CTypes;
  use Set;
  use Map;
  use Crypto;

  private config const logLevel = ServerConfig.logLevel;
  private config const logChannel = ServerConfig.logChannel;
  const jmLogger = new Logger(logLevel, logChannel);

  use CommandMap;

  proc fillSendBuffer(ref sendBuffer, ref data, ref destLocales, ref rowIndexInSendBuffer, ref numRowsToLoc, numColsThisType: int, numRowsInLocale: int) {
    forall i in 0..#numRowsInLocale with (ref sendBuffer, ref rowIndexInSendBuffer) {
      const destLoc = destLocales[i];
      const rowIdx = rowIndexInSendBuffer[i];

      for j in 0..#numColsThisType {

        // Copy the data from the local array to the send buffer for the destination locale
        sendBuffer[here.id][destLoc][rowIdx + j * numRowsToLoc[destLoc]] = data[i + j * numRowsInLocale];

      }
    }
  }

  proc joinMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
    param pn = Reflection.getRoutineName();

    var repMsg: string;
    const nArraysLeft = msgArgs["nArraysLeft"].toScalar(int),
      namesLeft = msgArgs["namesLeft"].toScalarArray(string, nArrays),
      nArraysRight = msgArgs["nArraysRight"].toScalar(int),
      namesRight = msgArgs["namesRight"].toScalarArray(string, nArrays),
      nMerging = msgArgs["nMerging"].toScalar(int),
      mergeLeft = msgArgs["mergeLeft"].toScalarArray(int, nMerging),
      mergeRight = msgArgs["mergeRight"].toScalarArray(int, nMerging)
      mergeHow = msgArgs["mergeHow"].toScalar(string), // "inner", "left", "right", or "outer"
      sortHow = msgArgs["sortHow"].toScalar(string); // "none", "pandas", or "columns"

    jmLogger.debug(getModuleName(), getRoutineName(), getLineNumber(),
                  "Joining two DataFrames on %i columns".format(nMerging));
    
    type arrayTypes = (int(8), int(16), int(32), int(64), uint(8), uint(16), uint(32), uint(64), bool, real(32), real(64), string);
    type cPtrTypes = (int(8), int(16), int(32), int(64), uint(8), uint(16), uint(32), uint(64), bool, real(32), real(64), int(64));

    var bytesPerType = [1, 2, 4, 8, 1, 2, 4, 8, 1, 4, 8, 0];

    var leftColCounts = 12 * int;
    var rightColCounts = 12 * int;
    var leftKeyInds = [0..#nMerging] 2 * int;
    var rightKeyInds = [0..#nMerging] 2 * int;

    var dtypeToIntMap = new map(DType, int);
    dtypeToIntMap[DType.Int8] = 0;
    dtypeToIntMap[DType.Int16] = 1;
    dtypeToIntMap[DType.Int32] = 2;
    dtypeToIntMap[DType.Int64] = 3;
    dtypeToIntMap[DType.UInt8] = 4;
    dtypeToIntMap[DType.UInt16] = 5;
    dtypeToIntMap[DType.UInt32] = 6;
    dtypeToIntMap[DType.UInt64] = 7;
    dtypeToIntMap[DType.Bool] = 8;
    dtypeToIntMap[DType.Float32] = 9;
    dtypeToIntMap[DType.Float64] = 10;
    dtypeToIntMap[DType.Strings] = 11;

    var typeToIntMap = new map(type, int);
    typeToIntMap[int(8)] = 0;
    typeToIntMap[int(16)] = 1;
    typeToIntMap[int(32)] = 2;
    typeToIntMap[int(64)] = 3;
    typeToIntMap[uint(8)] = 4;
    typeToIntMap[uint(16)] = 5;
    typeToIntMap[uint(32)] = 6;
    typeToIntMap[uint(64)] = 7;
    typeToIntMap[bool] = 8;
    typeToIntMap[real(32)] = 9;
    typeToIntMap[real(64)] = 10;
    typeToIntMap[string] = 11;

    var leftSize = -1;
    var rightSize = -1;

    var baseRowBytesLeft = 0;
    var baseKeyBytesLeft = 0;

    // We are going to store the hash of the key as a column. Then I don't have to recompute it.
    leftColCounts[3] += 1;

    for i in 0..#nArraysLeft {

      var genEntry = getGenericTypedArrayEntry(namesLeft[i], st);

      var dtype: DType = genEntry.dtype;
      leftColCounts[dtypeToIntMap[dtype]] += 1;
      var idx = mergeLeft.find(i);
      baseRowBytesLeft += bytesPerType[dtypeToIntMap[dtype]];

      if idx != -1 {
        leftKeyInds[idx] = (dtypeToIntMap[dtype], leftColCounts[dtypeToIntMap[dtype]] - 1);
        baseKeyBytesLeft += bytesPerType[dtypeToIntMap[dtype]];
      }

      if leftSize != -1  && genEntry.size != leftSize {

        const errMsg = "All columns in a given DataFrame must have the same size.";
        jmLogger.error(getModuleName(), pn, getLineNumber(), errMsg);
        return MsgTuple.error(errMsg);

      } else {
        leftSize = genEntry.size;
      }

    }

    var baseRowBytesRight = 0;
    var baseKeyBytesRight = 0;

    rightColCounts[3] += 1;

    for i in 0..#nArraysRight {

      var genEntry = getGenericTypedArrayEntry(namesRight[i], st);
      
      var dtype: DType = genEntry.dtype;
      rightColCounts[dtypeToIntMap[dtype]] += 1;
      var idx = mergeRight.find(i);
      baseRowBytesRight += bytesPerType[dtypeToIntMap[dtype]];

      if idx != -1 {
        rightKeyInds[idx] = (dtypeToIntMap[dtype], rightColCounts[dtypeToIntMap[dtype]] - 1);
        baseKeyBytesRight += bytesPerType[dtypeToIntMap[dtype]];
      }

      if rightSize != -1  && genEntry.size != rightSize {

        const errMsg = "All columns in a given DataFrame must have the same size.";
        jmLogger.error(getModuleName(), pn, getLineNumber(), errMsg);
        return MsgTuple.error(errMsg);

      } else {
        rightSize = genEntry.size;
      }

    }

    for i in 0..#nMerging {
      if leftKeyInds[i][0] != rightKeyInds[i][0] {
        const errMsg = "All corresponding merge columns must have the same type.";
        jmLogger.error(getModuleName(), pn, getLineNumber(), errMsg);
        return MsgTuple.error(errMsg);
      }
    }

    var leftDataRefs: [PrivateSpace] [0..11] c_ptr(void);
    var rightDataRefs: [PrivateSpace] [0..11] c_ptr(void);
    var leftNumElemsPerLocale: [PrivateSpace] int;
    var rightNumElemsPerLocale: [PrivateSpace] int;
    var leftSampleArray = makeDistArray(leftSize, int); // I need to set up a sample distributed array
    var rightSampleArray = makeDistArray(rightSize, int); // I can use this to quickly figure out how many values are on each locale
    var leftStrBytes: [PrivateSpace] list(uint(8));
    var rightStrBytes: [PrivateSpace] list(uint(8));
    var destLocByRowLeft: [PrivateSpace] list(int);
    var destLocByRowRight: [PrivateSpace] list(int);
    var numRowsSendingLeftByLoc: [PrivateSpace] [0..#numLocales] int;
    var numRowsSendingRightByLoc: [PrivateSpace] [0..#numLocales] int;
    var numStrBytesSendingLeftByLoc: [PrivateSpace] [0..#numLocales] int;
    var numStrBytesSendingRightByLoc: [PrivateSpace] [0..#numLocales] int;
    var maxRowsSendingLeft = 0;
    var maxRowsSendingRight = 0;
    var maxBytesSendingLeft = 0;
    var maxBytesSendingRight = 0;
    var rowIndexInLocLeft: [PrivateSpace] list(int);
    var rowIndexInLocRIght: [PrivateSPace] list(int);
    var byteOffsetInLocLeft: [PrivateSpace] list(int);
    var byteOffsetInLocRight: [PrivateSpace] list(int);

    coforall loc in Locales do on loc
      with (max reduce maxRowsSendingLeft, max reduce maxRowsSendingRight, max reduce maxBytesSendingLeft, max reduce maxBytesSendingRight) {

      leftNumElemsPerLocale[here.id] = leftSampleArray.localSubdomain().size;
      rightNumElemsPerLocale[here.id] = rightSampleArray.localSubdomain().size;

      var leftStrBytesBufferOffsets: [0..#leftColCounts[11]] int;
      var rightStrBytesBufferOffsets: [0..#rightColCounts[11]] int;

      for t in arrayTypes {
        var typeNum = typesToIntMap[t];
        type ct = cPtrTypes[typeNum];
        var leftArr: [0..#(leftNumElemsPerLocale[here.id]*leftColCounts[typeNum])] ct;
        leftDataRefs[here.id][typeNum] = c_addrOf(leftArr);
        var rightArr: [0..#(rightNumElemsPerLocale[here.id]*rightColCounts[typeNum])] ct;
        rightDataRefs[here.id][typeNum] = c_addrOf(rightArr);
      }

      var leftColsProcessed: [0..11] int;
      var rightColsProcessed: [0..11] int;

      for i in 0..#nArraysLeft {

        var dtype: DType = getGenericTypedArrayEntry(namesLeft[i], st).dtype;
        var ind = dtypeToIntMap[dtype];

        if ind < 11 {
          var arr = st[namesLeft[i]]: borrowed SymEntry(arrayTypes[ind], 1);
          var currBlock = leftColsProcessed[ind];
          ref arr = (leftDataRefs[here.id][ind]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[ind])] cPtrTypes[ind])).deref();
          arr[currblock*leftNumElemsPerLocale[here.id]..#leftNumElemsPerLocale[here.id]] = arr.a.localSlice[arr.a.domain.localSubdomain()];
          leftColsProcessed[ind] += 1;
        } else {
          var (strName, _) = namesLeft[i].splitMsgToTuple('+', 2);
          var segString = getSegString(strName, st);
          const offsetsDom = segString.offsets.a.domain.localSubdomain();
          ref globalOffsets = segString.offsets.a;
          var currBlock = leftColsProcessed[ind];
          ref arr = (leftDataRefs[here.id][ind]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[ind])] cPtrTypes[ind])).deref();
          var offsets = segString.offsets.a.localSlice[offsetsDom];
          var offsets2 = offsets - offsets[0] + arr[leftNumElemsPerLocale[here.id]*currBlock - (if currBlock > 0 then 1 else 0)];
          var topEnd = if offsetsDom.high >= segString.offsets.a.domain.high then segString.values.a.size else globalOffsets[offsetsDom.high + 1];
          var topEnd2 = topEnd - offsets[0] + arr[leftNumElemsPerLocale[here.id]*currBlock - (if currBlock > 0 then 1 else 0)];
          leftStrBytesBufferOffsets[currBlock] = topEnd2;
          arr[currblock*leftNumElemsPerLocale[here.id]..#leftNumElemsPerLocale[here.id]] = offsets2;
          var byteData = segString.values.a[offsets[0]..<topEnd];
          if currBlock == 0 {
            leftStrBytes[here.id] = new list(byteData);
          } else {
            leftStrBytes[here.id].pushBack(byteData);
          }
          leftColsProcessed[ind] += 1;
        }

      }

      for i in 0..#nArraysRight {

        var dtype: DType = getGenericTypedArrayEntry(namesRight[i], st).dtype;
        var ind = dtypeToIntMap[dtype];

        if ind < 11 {
          var arr = st[namesRight[i]]: borrowed SymEntry(arrayTypes[ind], 1);
          var currBlock = rightColsProcessed[ind];
          ref arr = (rightDataRefs[here.id][ind]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[ind])] cPtrTypes[ind])).deref();
          arr[currblock*rightNumElemsPerLocale[here.id]..#rightNumElemsPerLocale[here.id]] = arr.a.localSlice[arr.a.domain.localSubdomain()];
          rightColsProcessed[ind] += 1;
        } else {
          var (strName, _) = namesRight[i].splitMsgToTuple('+', 2);
          var segString = getSegString(strName, st);
          const offsetsDom = segString.offsets.a.domain.localSubdomain();
          ref globalOffsets = segString.offsets.a;
          var currBlock = rightColsProcessed[ind];
          ref arr = (rightDataRefs[here.id][ind]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[ind])] cPtrTypes[ind])).deref();
          var offsets = segString.offsets.a.localSlice[offsetsDom];
          var offsets2 = offsets - offsets[0] + arr[rightNumElemsPerLocale[here.id]*currBlock - (if currBlock > 0 then 1 else 0)];
          var topEnd = if offsetsDom.high >= segString.offsets.a.domain.high then segString.values.a.size else globalOffsets[offsetsDom.high + 1];
          var topEnd2 = topEnd - offsets[0] + arr[rightNumElemsPerLocale[here.id]*currBlock - (if currBlock > 0 then 1 else 0)];
          rightStrBytesBufferOffsets[currBlock] = topEnd2;
          arr[currblock*rightNumElemsPerLocale[here.id]..#rightNumElemsPerLocale[here.id]] = offsets2;
          var byteData = segString.values.a[offsets[0]..<topEnd];
          if currBlock == 0 {
            rightStrBytes[here.id] = new list(byteData);
          } else {
            rightStrBytes[here.id].pushBack(byteData);
          }
          rightColsProcessed[ind] += 1;
        }

      }

      var destLocsLeft: [0..#leftNumElemsPerLocale[here.id]] int;
      var strBytesByRowLeft: [0..#leftNumElemsPerLocale[here.id]] int;
      var strBytesByElemLeft: [0..#(leftNumElemsPerLocale[here.id] * leftColCounts[11])] int;
      var strBytesArrLeft = leftStrBytes[here.id].toArray();

      forall i in 0..#leftNumElemsPerLocale[here.id] {

        var strBytesThisRow = 0;
        var keyStrBytesThisRow = 0;
        ref arr = (leftDataRefs[here.id][11]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[11])] int(64))).deref();

        for j in 0..#leftColCounts[11] {

          var start = arr[j * leftNumElemsPerLocale[here.id] + i];
          var end = (if i == leftNumElemsPerLocale[here.id] - 1 then leftStrBytesBufferOffsets[j] else arr[j * leftNumElemsPerLocale[here.id] + i + 1]);
          strBytesThisRow += end - start;
          strBytesByElemLeft[j * leftNumElemsPerLocale[here.id] + i] = end - start;

        }

        strBytesByRowLeft[i] = strBytesThisRow;

        for j in 0..#nMerging {

          var currKey = leftKeyInds[j];
          if currKey[0] == 11 {
            var col = currKey[1];
            var start = arr[col * leftNumElemsPerLocale[here.id] + i];
            var end = (if i == leftNumElemsPerLocale[here.id] - 1 then leftStrBytesBufferOffsets[j] else arr[col * leftNumElemsPerLocale[here.id] + i + 1]);
            keyStrBytesThisRow += end - start;
          }

        }

        var keyBytes: [0..#(baseKeyBytesLeft + keyStrBytesThisRow)] uint(8);
        var currByte = 0;

        for j in 0..#nMerging {

          var currKey = leftKeyInds[j];
          dtypeInd = currKey[0];
          col = currKey[1];
          ref arr = (leftDataRefs[here.id][dtypeInd]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[dtypeInd])] cPtrTypes[dtypeInd])).deref();
          var ptr = c_ptrTo(arr): c_ptr(uint(8));

          if dtypeInd != 11 {

            var b = bytesPerType[dtypeInd];
            keyBytes[currByte..#b] = ptr[b * (leftNumElemsPerLocale[here.id] * col + i)..#b];
            currByte += b;

          } else {

            var start = arr[col * leftNumElemsPerLocale[here.id] + i];
            var end = (if i == leftNumElemsPerLocale[here.id] - 1 then leftStrBytesBufferOffsets[j] else arr[col * leftNumElemsPerLocale[here.id] + i]);
            keyBytes[currByte..#(end - start)] = strBytesArrLeft[start..<end];
            currByte += end - start;

          }

        }

        // And here you have it - all that to hash the key and figure out what locale it maps to!
        const h = keyBytes.hash();
        ref arr = (leftDataRefs[here.id][3]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[3])] int(64))).deref();
        arr[leftNumElemsPerLocale[here.id]*(leftColCounts[3] - 1) + i] = h;

        var destLoc = h % numLocales;
        destLocsLeft[i] = destLoc;

      }

      var destLocsRight: [0..#rightNumElemsPerLocale[here.id]] int;
      var strBytesByRowRight: [0..#rightNumElemsPerLocale[here.id]] int;
      var strBytesByElemRight: [0..#(rightNumElemsPerLocale[here.id] * rightColCounts[11])] int;
      var strBytesArrRight = rightStrBytes[here.id].toArray();

      forall i in 0..#rightNumElemsPerLocale[here.id] {

        var strBytesThisRow = 0;
        var keyStrBytesThisRow = 0;
        ref arr = (rightDataRefs[here.id][11]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[11])] int(64))).deref();

        for j in 0..#rightColCounts[11] {

          var start = arr[j * rightNumElemsPerLocale[here.id] + i];
          var end = (if i == rightNumElemsPerLocale[here.id] - 1 then rightStrBytesBufferOffsets[j] else arr[j * rightNumElemsPerLocale[here.id] + i + 1]);
          strBytesThisRow += end - start;
          strBytesByElemRight[j * rightNumElemsPerLocale[here.id] + i] = end - start;

        }

        strBytesByRowRight[i] = strBytesThisRow;

        for j in 0..#nMerging {

          var currKey = rightKeyInds[j];
          if currKey[0] == 11 {
            var col = currKey[1];
            var start = arr[col * rightNumElemsPerLocale[here.id] + i];
            var end = (if i == rightNumElemsPerLocale[here.id] - 1 then rightStrBytesBufferOffsets[j] else arr[col * rightNumElemsPerLocale[here.id] + i + 1]);
            keyStrBytesThisRow += end - start;
          }

        }

        var keyBytes: [0..#(baseKeyBytesRight + keyStrBytesThisRow)] uint(8);
        var currByte = 0;

        for j in 0..#nMerging {

          var currKey = rightKeyInds[j];
          dtypeInd = currKey[0];
          col = currKey[1];
          ref arr = (rightDataRefs[here.id][dtypeInd]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[dtypeInd])] cPtrTypes[dtypeInd])).deref();
          var ptr = c_ptrTo(arr): c_ptr(uint(8));

          if dtypeInd != 11 {

            var b = bytesPerType[dtypeInd];
            keyBytes[currByte..#b] = ptr[b * (rightNumElemsPerLocale[here.id] * col + i)..#b];
            currByte += b;

          } else {

            var start = arr[col * rightNumElemsPerLocale[here.id] + i];
            var end = (if i == rightNumElemsPerLocale[here.id] - 1 then rightStrBytesBufferOffsets[j] else arr[col * rightNumElemsPerLocale[here.id] + i + 1]);
            keyBytes[currByte..#(end - start)] = strBytesArrRight[start..<end];
            currByte += end - start;

          }

        }

        const h = keyBytes.hash();
        ref arr = (rightDataRefs[here.id][3]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[3])] int(64))).deref();
        arr[rightNumElemsPerLocale[here.id]*(rightColCounts[3] - 1) + i] = h;

        var destLoc = h % numLocales;
        destLocsRight[i] = destLoc;

      }

      var myNumRowsLeftByLocale: [0..#numLocales] int;
      var myNumBytesLeftByLocale: [0..#numLocales] int;
      var myNumRowsRightByLocale: [0..#numLocales] int;
      var myNumBytesRightByLocale: [0..#numLocales] int;
      var myRowIndexInLocLeft: [0..#leftNumElemsPerLocale[here.id]] int;
      var myRowIndexInLocRight: [0..#rightNumElemsPerLocale[here.id]] int;
      var myByteOffsetInLocLeft: [0..#(leftNumElemsPerLocale[here.id] * leftColCounts[11])];
      var myByteOffsetInLocRight: [0..#(rightNumElemsPerLocale[here.id] * rightColCounts[11])];

      for i in 0..#numLocales {

        var leftRowIndicator = [forall j in 0..#leftNumElemsPerLocale[here.id] do (if destLocsLeft[j] == i then 1 else 0)];
        var leftBytesCounter = [forall j in 0..#leftNumElemsPerLocale[here.id] do (if destLocsLeft[j] == i then strBytesByRowLeft[j] else 0)];
        var leftSizesThisLoc = [forall j in 0..#(leftNumElemsPerLocale[here.id] * leftColCounts[11]) do (if destLocsLeft[j%leftNumElemsPerLocale[here.id]] == i then strBytesByElemLeft[j] else 0)];
        var rightRowIndicator = [forall j in 0..#rightNumElemsPerLocale[here.id] do (if destLocsRight[j] == i then 1 else 0)];
        var rightBytesCounter = [forall j in 0..#rightNumElemsPerLocale[here.id] do (if destLocsRight[j] == i then strBytesByRowRight[j] else 0)];
        var rightSizesThisLoc = [forall j in 0..#(rightNumElemsPerLocale[here.id] * rightColCounts[11]) do (if destLocsRight[j%rightNumElemsPerLocale[here.id]] == i then strBytesByElemRight[j] else 0)];

        myNumRowsLeftByLocale[i] = + reduce leftRowIndicator;
        myNumBytesLeftByLocale[i] = + reduce leftBytesCounter;
        myNumRowsRightByLocale[i] = + reduce rightRowIndicator;
        myNumBytesRightByLocale[i] = + reduce rightBytesCounter;

        myRowIndexInLocLeft += (+ scan leftRowIndicator) - leftRowIndicator;
        myByteOffsetInLocLeft += (+ scan leftSizesThisLoc) - leftSizesThisLoc;
        myRowIndexInLocRight += (+ scan rightRowIndicator) - rightRowIndicator;
        myByteOffsetInLocRight ++ (+ scan rightSizesThisLoc) - rightSizesThisLoc;

      }

      maxRowsSendingLeft = max reduce myNumRowsLeftByLocale;
      maxBytesSendingLeft = max reduce myNumBytesLeftByLocale;
      maxRowsSendingRight = max reduce myNumRowsRightByLocale;
      maxBytesSendingRight = max reduce myNumBytesRightByLocale;

      destLocByRowLeft[here.id] = new list(destLocsLeft);
      destLocByRowRight[here.id] = new list(destLocsRight);
      rowIndexInLocLeft[here.id] = new list(myRowIndexInLocLeft);
      rowIndexInLocRight[here.id] = new list(myRowIndexInLocRight);
      byteOffsetInLocLeft[here.id] = new list(myByteOffsetInLocLeft);
      byteOffsetInLocRight[here.id] = new list(myByteOffsetInLocRight);
      numRowsSendingLeftByLoc[here.id] = myNumRowsLeftByLocale;
      numRowsSendingRightByLoc[here.id] = myNumRowsRightByLocale;
      numStrBytesSendingLeftByLoc[here.id] = myNumBytesLeftByLocale;
      numStrBytesSendingRightByLoc[here.id] = myNumBytesRightByLocale;

    }

    int8LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[0])] int(8);
    int16LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[1])] int(16);
    int32LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[2])] int(32);
    int64LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[3])] int(64);
    uint8LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[4])] uint(8);
    uint16LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[5])] uint(16);
    uint32LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[6])] uint(32);
    uint64LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[7])] uint(64);
    boolLeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[8])] bool;
    real32LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[9])] real(32);
    real64LeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[10])] real(64);
    stringOffsetLeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[11])] int;
    stringBytesLeftSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxBytesSendingLeft)] uint(8);

    int8RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[0])] int(8);
    int16RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[1])] int(16);
    int32RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[2])] int(32);
    int64RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[3])] int(64);
    uint8RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[4])] uint(8);
    uint16RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[5])] uint(16);
    uint32RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[6])] uint(32);
    uint64RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[7])] uint(64);
    boolRightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[8])] bool;
    real32RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[9])] real(32);
    real64RightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[10])] real(64);
    stringOffsetRightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[11])] int;
    stringBytesRightSendBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxBytesSendingRight)] uint(8);

    int8LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[0])] int(8);
    int16LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[1])] int(16);
    int32LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[2])] int(32);
    int64LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[3])] int(64);
    uint8LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[4])] uint(8);
    uint16LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[5])] uint(16);
    uint32LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[6])] uint(32);
    uint64LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[7])] uint(64);
    boolLeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[8])] bool;
    real32LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[9])] real(32);
    real64LeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[10])] real(64);
    stringOffsetLeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingLeft * leftColCounts[11])] int;
    stringBytesLeftRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxBytesSendingLeft)] uint(8);

    int8RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[0])] int(8);
    int16RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[1])] int(16);
    int32RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[2])] int(32);
    int64RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[3])] int(64);
    uint8RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[4])] uint(8);
    uint16RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[5])] uint(16);
    uint32RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[6])] uint(32);
    uint64RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[7])] uint(64);
    boolRightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[8])] bool;
    real32RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[9])] real(32);
    real64RightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[10])] real(64);
    stringOffsetRightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxRowsSendingRight * rightColCounts[11])] int;
    stringBytesRightRecvBuffer: [PrivateSpace] [0..#numLocales] [0..#(maxBytesSendingRight)] uint(8);

    coforall loc in Locales do on loc {

      var myDestLocByRowLeft = destLocByRowLeft[here.id].toArray();
      var myRowIndexInLocLeft = rowIndexInLocLeft[here.id].toArray();

      ref arr = (leftDataRefs[here.id][0]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[0])] int(8))).deref();
      fillSendBuffer(int8LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[0], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][1]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[1])] int(16))).deref();
      fillSendBuffer(int16LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[1], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][2]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[2])] int(32))).deref();
      fillSendBuffer(int32LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[2], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][3]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[3])] int(64))).deref();
      fillSendBuffer(int64LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[3], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][4]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[4])] uint(8))).deref();
      fillSendBuffer(uint8LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[4], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][5]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[5])] uint(16))).deref();
      fillSendBuffer(uint16LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[5], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][6]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[6])] uint(32))).deref();
      fillSendBuffer(uint32LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[6], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][7]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[7])] uint(64))).deref();
      fillSendBuffer(uint64LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[7], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][8]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[8])] bool)).deref();
      fillSendBuffer(boolLeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[8], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][9]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[9])] real(32))).deref();
      fillSendBuffer(real32LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[9], leftNumElemsPerLocale[here.id]);
      arr = (leftDataRefs[here.id][10]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[10])] real(64))).deref();
      fillSendBuffer(real64LeftSendBuffer, arr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[10], leftNumElemsPerLocale[here.id]);

      var offsetArr = byteOffsetInLocLeft[here.id].toArray();
      fillSendBuffer(stringOffsetLeftSendBuffer, offsetArr, myDestLocByRowLeft, myRowIndexInLocLeft, numRowsSendingLeftByLoc[here.id], leftColCounts[11], leftNumElemsPerLocale[here.id]);
      
      arr = (leftDataRefs[here.id][11]:c_ptr([0..#(leftNumElemsPerLocale[here.id]*leftColCounts[11])] int(64))).deref();
      var strBytesArrLeft = leftStrBytes[here.id].toArray();

      forall i in 0..#(leftNumElemsPerLocale[here.id] * leftColCounts[11]) with (ref stringOffsetLeftSendBuffer, ref myRowIndexInLocLeft) {

        const destLoc = myDestLocByRowLeft[i % leftNumElemsPerLocale[here.id]];
        const startStrArr = arr[i];
        const endStrArr = (if i != leftNumElemsPerLocale[here.id] * leftColCounts[11] - 1 then arr[i + 1] else leftStrBytesBufferOffsets[leftColCounts[11] - 1]);
        const startOnLoc = offsetArr[i];
        const endOnLoc = startOnLoc + (endStrArr - startStrArr);
        stringBytesLeftSendBuffer[startOnLoc..<endOnLoc] = strBytesArrLeft[startStrArr..<endStrArr];

      }

      // Theoretically, this might be slow because we are transferring more data than we need to.
      // However, I don't really want to calculate out how much is actually getting transferred. So if it's slow, I'll fix it.

      forall i in 0..#numLocales {
        int8LeftRecvBuffer[i][here.id] = int8LeftSendBuffer[here.id][i];
        int16LeftRecvBuffer[i][here.id] = int16LeftSendBuffer[here.id][i];
        int32LeftRecvBuffer[i][here.id] = int32LeftSendBuffer[here.id][i];
        int64LeftRecvBuffer[i][here.id] = int64LeftSendBuffer[here.id][i];
        uint8LeftRecvBuffer[i][here.id] = uint8LeftSendBuffer[here.id][i];
        uint16LeftRecvBuffer[i][here.id] = uint16LeftSendBuffer[here.id][i];
        uint32LeftRecvBuffer[i][here.id] = uint32LeftSendBuffer[here.id][i];
        uint64LeftRecvBuffer[i][here.id] = uint64LeftSendBuffer[here.id][i];
        boolLeftRecvBuffer[i][here.id] = boolLeftSendBuffer[here.id][i];
        real32LeftRecvBuffer[i][here.id] = real32LeftSendBuffer[here.id][i];
        real64LeftRecvBuffer[i][here.id] = real64LeftSendBuffer[here.id][i];
        stringOffsetLeftRecvBuffer[i][here.id] = stringOffsetLeftSendBuffer[here.id][i];
        stringBytesLeftRecvBuffer[i][here.id] = stringBytesLeftSendBuffer[here.id][i];
      }

      var myDestLocByRowRight = destLocByRowRight[here.id].toArray();
      var myRowIndexInLocRight = rowIndexInLocRight[here.id].toArray();

      arr = (rightDataRefs[here.id][0]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[0])] int(8))).deref();
      fillSendBuffer(int8RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[0], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][1]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[1])] int(16))).deref();
      fillSendBuffer(int16RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[1], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][2]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[2])] int(32))).deref();
      fillSendBuffer(int32RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[2], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][3]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[3])] int(64))).deref();
      fillSendBuffer(int64RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[3], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][4]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[4])] uint(8))).deref();
      fillSendBuffer(uint8RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[4], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][5]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[5])] uint(16))).deref();
      fillSendBuffer(uint16RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[5], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][6]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[6])] uint(32))).deref();
      fillSendBuffer(uint32RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[6], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][7]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[7])] uint(64))).deref();
      fillSendBuffer(uint64RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[7], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][8]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[8])] bool)).deref();
      fillSendBuffer(boolRightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[8], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][9]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[9])] real(32))).deref();
      fillSendBuffer(real32RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[9], rightNumElemsPerLocale[here.id]);
      arr = (rightDataRefs[here.id][10]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[10])] real(64))).deref();
      fillSendBuffer(real64RightSendBuffer, arr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[10], rightNumElemsPerLocale[here.id]);

      offsetArr = byteOffsetInLocRight[here.id].toArray();
      fillSendBuffer(stringOffsetRightSendBuffer, offsetArr, myDestLocByRowRight, myRowIndexInLocRight, numRowsSendingRightByLoc[here.id], rightColCounts[11], rightNumElemsPerLocale[here.id]);
      
      arr = (rightDataRefs[here.id][11]:c_ptr([0..#(rightNumElemsPerLocale[here.id]*rightColCounts[11])] int(64))).deref();
      var strBytesArrRight = rightStrBytes[here.id].toArray();

      forall i in 0..#(rightNumElemsPerLocale[here.id] * rightColCounts[11]) with (ref stringOffsetRightSendBuffer, ref myRowIndexInLocRight) {

        const destLoc = myDestLocByRowRight[i % rightNumElemsPerLocale[here.id]];
        const startStrArr = arr[i];
        const endStrArr = (if i != rightNumElemsPerLocale[here.id] * rightColCounts[11] - 1 then arr[i + 1] else rightStrBytesBufferOffsets[rightColCounts[11] - 1]);
        const startOnLoc = offsetArr[i];
        const endOnLoc = startOnLoc + (endStrArr - startStrArr);
        stringBytesRightSendBuffer[startOnLoc..<endOnLoc] = strBytesArrRight[startStrArr..<endStrArr];

      }

      forall i in 0..#numLocales {
        int8RightRecvBuffer[i][here.id] = int8RightSendBuffer[here.id][i];
        int16RightRecvBuffer[i][here.id] = int16RightSendBuffer[here.id][i];
        int32RightRecvBuffer[i][here.id] = int32RightSendBuffer[here.id][i];
        int64RightRecvBuffer[i][here.id] = int64RightSendBuffer[here.id][i];
        uint8RightRecvBuffer[i][here.id] = uint8RightSendBuffer[here.id][i];
        uint16RightRecvBuffer[i][here.id] = uint16RightSendBuffer[here.id][i];
        uint32RightRecvBuffer[i][here.id] = uint32RightSendBuffer[here.id][i];
        uint64RightRecvBuffer[i][here.id] = uint64RightSendBuffer[here.id][i];
        boolRightRecvBuffer[i][here.id] = boolRightSendBuffer[here.id][i];
        real32RightRecvBuffer[i][here.id] = real32RightSendBuffer[here.id][i];
        real64RightRecvBuffer[i][here.id] = real64RightSendBuffer[here.id][i];
        stringOffsetRightRecvBuffer[i][here.id] = stringOffsetRightSendBuffer[here.id][i];
        stringBytesRightRecvBuffer[i][here.id] = stringBytesRightSendBuffer[here.id][i];
      }

    }

    coforall loc in Locales do on loc {

    }

    return new MsgTuple(repMsg, MsgType.NORMAL);
  }
  registerFunction("join", joinMsg, getModuleName());

}