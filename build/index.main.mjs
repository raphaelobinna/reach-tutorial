// Automatically generated with Reach 0.1.11 (a9f7613d)
/* eslint-disable */
export const _version = '0.1.11';
export const _versionHash = '0.1.11 (a9f7613d)';
export const _backendVersion = 17;

export function getExports(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getEvents(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getViews(s, viewlib) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Address;
  const ctc1 = stdlib.T_UInt;
  const ctc2 = stdlib.T_Digest;
  
  return {
    infos: {
      },
    views: {
      1: [ctc0, ctc1, ctc1, ctc1],
      5: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc1],
      7: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc2, ctc1],
      9: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc2, ctc1, ctc1]
      }
    };
  
  };
export function _getMaps(s) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Tuple([]);
  return {
    mapDataTy: ctc0
    };
  };
export async function Alice(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for Alice expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for Alice expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Tuple([ctc0, ctc0]);
  const ctc2 = stdlib.T_Digest;
  const ctc3 = stdlib.T_Null;
  const ctc4 = stdlib.T_Address;
  
  
  const v294 = stdlib.protect(ctc0, interact.deadline, 'for Alice\'s interact field deadline');
  const v295 = stdlib.protect(ctc0, interact.wager, 'for Alice\'s interact field wager');
  
  const txn1 = await (ctc.sendrecv({
    args: [v295, v294],
    evt_cnt: 2,
    funcNum: 0,
    lct: stdlib.checkedBigNumberify('./index.rsh:53:13:dot', stdlib.UInt_max, '0'),
    onlyIf: true,
    out_tys: [ctc0, ctc0],
    pay: [v295, []],
    sim_p: (async (txn1) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v299, v300], secs: v302, time: v301, didSend: v56, from: v298 } = txn1;
      
      sim_r.txns.push({
        amt: v299,
        kind: 'to',
        tok: undefined /* Nothing */
        });
      const v311 = stdlib.add(v301, v300);
      sim_r.isHalt = false;
      
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: undefined /* mto */,
    tys: [ctc0, ctc0],
    waitIfNotPresent: false
    }));
  const {data: [v299, v300], secs: v302, time: v301, didSend: v56, from: v298 } = txn1;
  ;
  const v311 = stdlib.add(v301, v300);
  const txn2 = await (ctc.recv({
    didSend: false,
    evt_cnt: 0,
    funcNum: 1,
    out_tys: [],
    timeoutAt: ['time', v311],
    waitIfNotPresent: false
    }));
  if (txn2.didTimeout) {
    const txn3 = await (ctc.sendrecv({
      args: [v298, v299, v300, v311],
      evt_cnt: 0,
      funcNum: 2,
      lct: v301,
      onlyIf: true,
      out_tys: [],
      pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
      sim_p: (async (txn3) => {
        const sim_r = { txns: [], mapRefs: [], maps: [] };
        let sim_txn_ctr = stdlib.UInt_max;
        const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
        
        
        const {data: [], secs: v455, time: v454, didSend: v247, from: v453 } = txn3;
        
        ;
        sim_r.txns.push({
          kind: 'from',
          to: v298,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        
        return sim_r;
        }),
      soloSend: false,
      timeoutAt: undefined /* mto */,
      tys: [ctc4, ctc0, ctc0, ctc0],
      waitIfNotPresent: false
      }));
    const {data: [], secs: v455, time: v454, didSend: v247, from: v453 } = txn3;
    ;
    ;
    stdlib.protect(ctc3, await interact.informTimeout(), {
      at: './index.rsh:45:55:application',
      fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:63:53:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
      msg: 'informTimeout',
      who: 'Alice'
      });
    
    return;
    
    }
  else {
    const {data: [], secs: v317, time: v316, didSend: v65, from: v315 } = txn2;
    const v319 = stdlib.add(v299, v299);
    ;
    let v320 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
    let v321 = v316;
    let v328 = v319;
    
    while (await (async () => {
      const v336 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
      
      return v336;})()) {
      const v343 = stdlib.add(v321, v300);
      const v347 = stdlib.protect(ctc0, await interact.getHand(), {
        at: './index.rsh:73:37:application',
        fs: ['at ./index.rsh:72:19:application call to [unknown function] (defined at: ./index.rsh:72:23:function exp)'],
        msg: 'getHand',
        who: 'Alice'
        });
      const v348 = stdlib.protect(ctc0, await interact.random(), {
        at: 'reach standard library:64:31:application',
        fs: ['at ./index.rsh:74:58:application call to "makeCommitment" (defined at: reach standard library:63:8:function exp)', 'at ./index.rsh:72:19:application call to [unknown function] (defined at: ./index.rsh:72:23:function exp)'],
        msg: 'random',
        who: 'Alice'
        });
      const v349 = stdlib.digest(ctc1, [v348, v347]);
      
      const txn3 = await (ctc.sendrecv({
        args: [v298, v299, v300, v315, v328, v343, v349],
        evt_cnt: 1,
        funcNum: 4,
        lct: v321,
        onlyIf: true,
        out_tys: [ctc2],
        pay: [stdlib.checkedBigNumberify('./index.rsh:77:15:decimal', stdlib.UInt_max, '0'), []],
        sim_p: (async (txn3) => {
          const sim_r = { txns: [], mapRefs: [], maps: [] };
          let sim_txn_ctr = stdlib.UInt_max;
          const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
          
          
          const {data: [v352], secs: v354, time: v353, didSend: v91, from: v351 } = txn3;
          
          ;
          const v362 = stdlib.add(v353, v300);
          sim_r.isHalt = false;
          
          return sim_r;
          }),
        soloSend: true,
        timeoutAt: ['time', v343],
        tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2],
        waitIfNotPresent: false
        }));
      if (txn3.didTimeout) {
        const txn4 = await (ctc.sendrecv({
          args: [v298, v299, v300, v315, v328, v343],
          evt_cnt: 0,
          funcNum: 5,
          lct: v321,
          onlyIf: true,
          out_tys: [],
          pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn4) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [], secs: v427, time: v426, didSend: v206, from: v425 } = txn4;
            
            ;
            sim_r.txns.push({
              kind: 'from',
              to: v315,
              tok: undefined /* Nothing */
              });
            sim_r.txns.push({
              kind: 'halt',
              tok: undefined /* Nothing */
              })
            sim_r.isHalt = true;
            
            return sim_r;
            }),
          soloSend: false,
          timeoutAt: undefined /* mto */,
          tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0],
          waitIfNotPresent: false
          }));
        const {data: [], secs: v427, time: v426, didSend: v206, from: v425 } = txn4;
        ;
        const v428 = stdlib.addressEq(v298, v425);
        const v429 = stdlib.addressEq(v315, v425);
        const v430 = v428 ? true : v429;
        stdlib.assert(v430, {
          at: 'reach standard library:200:11:dot',
          fs: ['at ./index.rsh:78:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
          msg: 'sender correct',
          who: 'Alice'
          });
        ;
        stdlib.protect(ctc3, await interact.informTimeout(), {
          at: './index.rsh:45:55:application',
          fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:78:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
          msg: 'informTimeout',
          who: 'Alice'
          });
        
        return;
        
        }
      else {
        const {data: [v352], secs: v354, time: v353, didSend: v91, from: v351 } = txn3;
        ;
        const v355 = stdlib.addressEq(v298, v351);
        stdlib.assert(v355, {
          at: './index.rsh:77:15:dot',
          fs: [],
          msg: 'sender correct',
          who: 'Alice'
          });
        const v362 = stdlib.add(v353, v300);
        const txn4 = await (ctc.recv({
          didSend: false,
          evt_cnt: 1,
          funcNum: 6,
          out_tys: [ctc0],
          timeoutAt: ['time', v362],
          waitIfNotPresent: false
          }));
        if (txn4.didTimeout) {
          const txn5 = await (ctc.sendrecv({
            args: [v298, v299, v300, v315, v328, v352, v362],
            evt_cnt: 0,
            funcNum: 7,
            lct: v353,
            onlyIf: true,
            out_tys: [],
            pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn5) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [], secs: v411, time: v410, didSend: v172, from: v409 } = txn5;
              
              ;
              sim_r.txns.push({
                kind: 'from',
                to: v298,
                tok: undefined /* Nothing */
                });
              sim_r.txns.push({
                kind: 'halt',
                tok: undefined /* Nothing */
                })
              sim_r.isHalt = true;
              
              return sim_r;
              }),
            soloSend: false,
            timeoutAt: undefined /* mto */,
            tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc2, ctc0],
            waitIfNotPresent: false
            }));
          const {data: [], secs: v411, time: v410, didSend: v172, from: v409 } = txn5;
          ;
          const v412 = stdlib.addressEq(v298, v409);
          const v413 = stdlib.addressEq(v315, v409);
          const v414 = v412 ? true : v413;
          stdlib.assert(v414, {
            at: 'reach standard library:200:11:dot',
            fs: ['at ./index.rsh:86:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
            msg: 'sender correct',
            who: 'Alice'
            });
          ;
          stdlib.protect(ctc3, await interact.informTimeout(), {
            at: './index.rsh:45:55:application',
            fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:86:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
            msg: 'informTimeout',
            who: 'Alice'
            });
          
          return;
          
          }
        else {
          const {data: [v368], secs: v370, time: v369, didSend: v101, from: v367 } = txn4;
          ;
          const v371 = stdlib.addressEq(v315, v367);
          stdlib.assert(v371, {
            at: './index.rsh:85:13:dot',
            fs: [],
            msg: 'sender correct',
            who: 'Alice'
            });
          const v378 = stdlib.add(v369, v300);
          const txn5 = await (ctc.sendrecv({
            args: [v298, v299, v300, v315, v328, v352, v368, v378, v348, v347],
            evt_cnt: 2,
            funcNum: 8,
            lct: v369,
            onlyIf: true,
            out_tys: [ctc0, ctc0],
            pay: [stdlib.checkedBigNumberify('./index.rsh:93:17:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn5) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [v383, v384], secs: v386, time: v385, didSend: v111, from: v382 } = txn5;
              
              ;
              const v390 = stdlib.sub(stdlib.checkedBigNumberify('./index.rsh:8:18:decimal', stdlib.UInt_max, '4'), v368);
              const v391 = stdlib.add(v384, v390);
              const v392 = stdlib.mod(v391, stdlib.checkedBigNumberify('./index.rsh:8:34:decimal', stdlib.UInt_max, '3'));
              const cv320 = v392;
              const cv321 = v385;
              const cv328 = v328;
              
              await (async () => {
                const v320 = cv320;
                const v321 = cv321;
                const v328 = cv328;
                
                if (await (async () => {
                  const v336 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
                  
                  return v336;})()) {
                  const v343 = stdlib.add(v321, v300);
                  sim_r.isHalt = false;
                  }
                else {
                  const v441 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '2'));
                  const v444 = stdlib.mul(stdlib.checkedBigNumberify('./index.rsh:104:12:decimal', stdlib.UInt_max, '2'), v299);
                  const v446 = v441 ? v298 : v315;
                  sim_r.txns.push({
                    kind: 'from',
                    to: v446,
                    tok: undefined /* Nothing */
                    });
                  sim_r.txns.push({
                    kind: 'halt',
                    tok: undefined /* Nothing */
                    })
                  sim_r.isHalt = true;
                  }})();
              return sim_r;
              }),
            soloSend: true,
            timeoutAt: ['time', v378],
            tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc2, ctc0, ctc0, ctc0, ctc0],
            waitIfNotPresent: false
            }));
          if (txn5.didTimeout) {
            const txn6 = await (ctc.sendrecv({
              args: [v298, v299, v300, v315, v328, v352, v368, v378],
              evt_cnt: 0,
              funcNum: 9,
              lct: v369,
              onlyIf: true,
              out_tys: [],
              pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
              sim_p: (async (txn6) => {
                const sim_r = { txns: [], mapRefs: [], maps: [] };
                let sim_txn_ctr = stdlib.UInt_max;
                const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
                
                
                const {data: [], secs: v395, time: v394, didSend: v138, from: v393 } = txn6;
                
                ;
                sim_r.txns.push({
                  kind: 'from',
                  to: v315,
                  tok: undefined /* Nothing */
                  });
                sim_r.txns.push({
                  kind: 'halt',
                  tok: undefined /* Nothing */
                  })
                sim_r.isHalt = true;
                
                return sim_r;
                }),
              soloSend: false,
              timeoutAt: undefined /* mto */,
              tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc2, ctc0, ctc0],
              waitIfNotPresent: false
              }));
            const {data: [], secs: v395, time: v394, didSend: v138, from: v393 } = txn6;
            ;
            const v396 = stdlib.addressEq(v298, v393);
            const v397 = stdlib.addressEq(v315, v393);
            const v398 = v396 ? true : v397;
            stdlib.assert(v398, {
              at: 'reach standard library:200:11:dot',
              fs: ['at ./index.rsh:94:57:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
              msg: 'sender correct',
              who: 'Alice'
              });
            ;
            stdlib.protect(ctc3, await interact.informTimeout(), {
              at: './index.rsh:45:55:application',
              fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:94:57:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
              msg: 'informTimeout',
              who: 'Alice'
              });
            
            return;
            
            }
          else {
            const {data: [v383, v384], secs: v386, time: v385, didSend: v111, from: v382 } = txn5;
            ;
            const v387 = stdlib.addressEq(v298, v382);
            stdlib.assert(v387, {
              at: './index.rsh:93:17:dot',
              fs: [],
              msg: 'sender correct',
              who: 'Alice'
              });
            const v388 = stdlib.digest(ctc1, [v383, v384]);
            const v389 = stdlib.digestEq(v352, v388);
            stdlib.assert(v389, {
              at: 'reach standard library:69:17:application',
              fs: ['at ./index.rsh:96:26:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
              msg: null,
              who: 'Alice'
              });
            const v390 = stdlib.sub(stdlib.checkedBigNumberify('./index.rsh:8:18:decimal', stdlib.UInt_max, '4'), v368);
            const v391 = stdlib.add(v384, v390);
            const v392 = stdlib.mod(v391, stdlib.checkedBigNumberify('./index.rsh:8:34:decimal', stdlib.UInt_max, '3'));
            const cv320 = v392;
            const cv321 = v385;
            const cv328 = v328;
            
            v320 = cv320;
            v321 = cv321;
            v328 = cv328;
            
            continue;}
          
          }
        
        }
      
      }
    const v441 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '2'));
    const v444 = stdlib.mul(stdlib.checkedBigNumberify('./index.rsh:104:12:decimal', stdlib.UInt_max, '2'), v299);
    const v446 = v441 ? v298 : v315;
    ;
    return;
    }
  
  
  
  };
export async function Bob(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for Bob expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for Bob expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Null;
  const ctc2 = stdlib.T_Digest;
  const ctc3 = stdlib.T_Tuple([ctc0, ctc0]);
  const ctc4 = stdlib.T_Address;
  
  
  const txn1 = await (ctc.recv({
    didSend: false,
    evt_cnt: 2,
    funcNum: 0,
    out_tys: [ctc0, ctc0],
    timeoutAt: undefined /* mto */,
    waitIfNotPresent: false
    }));
  const {data: [v299, v300], secs: v302, time: v301, didSend: v56, from: v298 } = txn1;
  ;
  const v311 = stdlib.add(v301, v300);
  stdlib.protect(ctc1, await interact.acceptWager(v299), {
    at: './index.rsh:59:29:application',
    fs: ['at ./index.rsh:58:15:application call to [unknown function] (defined at: ./index.rsh:58:19:function exp)'],
    msg: 'acceptWager',
    who: 'Bob'
    });
  
  const txn2 = await (ctc.sendrecv({
    args: [v298, v299, v300, v311],
    evt_cnt: 0,
    funcNum: 1,
    lct: v301,
    onlyIf: true,
    out_tys: [],
    pay: [v299, []],
    sim_p: (async (txn2) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [], secs: v317, time: v316, didSend: v65, from: v315 } = txn2;
      
      const v319 = stdlib.add(v299, v299);
      sim_r.txns.push({
        amt: v299,
        kind: 'to',
        tok: undefined /* Nothing */
        });
      const v320 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
      const v321 = v316;
      const v328 = v319;
      
      if (await (async () => {
        const v336 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
        
        return v336;})()) {
        const v343 = stdlib.add(v321, v300);
        sim_r.isHalt = false;
        }
      else {
        const v441 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '2'));
        const v444 = stdlib.mul(stdlib.checkedBigNumberify('./index.rsh:104:12:decimal', stdlib.UInt_max, '2'), v299);
        const v446 = v441 ? v298 : v315;
        sim_r.txns.push({
          kind: 'from',
          to: v446,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        }
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: ['time', v311],
    tys: [ctc4, ctc0, ctc0, ctc0],
    waitIfNotPresent: false
    }));
  if (txn2.didTimeout) {
    const txn3 = await (ctc.sendrecv({
      args: [v298, v299, v300, v311],
      evt_cnt: 0,
      funcNum: 2,
      lct: v301,
      onlyIf: true,
      out_tys: [],
      pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
      sim_p: (async (txn3) => {
        const sim_r = { txns: [], mapRefs: [], maps: [] };
        let sim_txn_ctr = stdlib.UInt_max;
        const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
        
        
        const {data: [], secs: v455, time: v454, didSend: v247, from: v453 } = txn3;
        
        ;
        sim_r.txns.push({
          kind: 'from',
          to: v298,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        
        return sim_r;
        }),
      soloSend: false,
      timeoutAt: undefined /* mto */,
      tys: [ctc4, ctc0, ctc0, ctc0],
      waitIfNotPresent: false
      }));
    const {data: [], secs: v455, time: v454, didSend: v247, from: v453 } = txn3;
    ;
    ;
    stdlib.protect(ctc1, await interact.informTimeout(), {
      at: './index.rsh:45:55:application',
      fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:63:53:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
      msg: 'informTimeout',
      who: 'Bob'
      });
    
    return;
    
    }
  else {
    const {data: [], secs: v317, time: v316, didSend: v65, from: v315 } = txn2;
    const v319 = stdlib.add(v299, v299);
    ;
    let v320 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
    let v321 = v316;
    let v328 = v319;
    
    while (await (async () => {
      const v336 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
      
      return v336;})()) {
      const v343 = stdlib.add(v321, v300);
      const txn3 = await (ctc.recv({
        didSend: false,
        evt_cnt: 1,
        funcNum: 4,
        out_tys: [ctc2],
        timeoutAt: ['time', v343],
        waitIfNotPresent: false
        }));
      if (txn3.didTimeout) {
        const txn4 = await (ctc.sendrecv({
          args: [v298, v299, v300, v315, v328, v343],
          evt_cnt: 0,
          funcNum: 5,
          lct: v321,
          onlyIf: true,
          out_tys: [],
          pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn4) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [], secs: v427, time: v426, didSend: v206, from: v425 } = txn4;
            
            ;
            sim_r.txns.push({
              kind: 'from',
              to: v315,
              tok: undefined /* Nothing */
              });
            sim_r.txns.push({
              kind: 'halt',
              tok: undefined /* Nothing */
              })
            sim_r.isHalt = true;
            
            return sim_r;
            }),
          soloSend: false,
          timeoutAt: undefined /* mto */,
          tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0],
          waitIfNotPresent: false
          }));
        const {data: [], secs: v427, time: v426, didSend: v206, from: v425 } = txn4;
        ;
        const v428 = stdlib.addressEq(v298, v425);
        const v429 = stdlib.addressEq(v315, v425);
        const v430 = v428 ? true : v429;
        stdlib.assert(v430, {
          at: 'reach standard library:200:11:dot',
          fs: ['at ./index.rsh:78:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
          msg: 'sender correct',
          who: 'Bob'
          });
        ;
        stdlib.protect(ctc1, await interact.informTimeout(), {
          at: './index.rsh:45:55:application',
          fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:78:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
          msg: 'informTimeout',
          who: 'Bob'
          });
        
        return;
        
        }
      else {
        const {data: [v352], secs: v354, time: v353, didSend: v91, from: v351 } = txn3;
        ;
        const v355 = stdlib.addressEq(v298, v351);
        stdlib.assert(v355, {
          at: './index.rsh:77:15:dot',
          fs: [],
          msg: 'sender correct',
          who: 'Bob'
          });
        const v362 = stdlib.add(v353, v300);
        const v366 = stdlib.protect(ctc0, await interact.getHand(), {
          at: './index.rsh:83:56:application',
          fs: ['at ./index.rsh:82:17:application call to [unknown function] (defined at: ./index.rsh:82:21:function exp)'],
          msg: 'getHand',
          who: 'Bob'
          });
        
        const txn4 = await (ctc.sendrecv({
          args: [v298, v299, v300, v315, v328, v352, v362, v366],
          evt_cnt: 1,
          funcNum: 6,
          lct: v353,
          onlyIf: true,
          out_tys: [ctc0],
          pay: [stdlib.checkedBigNumberify('./index.rsh:85:13:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn4) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [v368], secs: v370, time: v369, didSend: v101, from: v367 } = txn4;
            
            ;
            const v378 = stdlib.add(v369, v300);
            sim_r.isHalt = false;
            
            return sim_r;
            }),
          soloSend: true,
          timeoutAt: ['time', v362],
          tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc2, ctc0, ctc0],
          waitIfNotPresent: false
          }));
        if (txn4.didTimeout) {
          const txn5 = await (ctc.sendrecv({
            args: [v298, v299, v300, v315, v328, v352, v362],
            evt_cnt: 0,
            funcNum: 7,
            lct: v353,
            onlyIf: true,
            out_tys: [],
            pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn5) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [], secs: v411, time: v410, didSend: v172, from: v409 } = txn5;
              
              ;
              sim_r.txns.push({
                kind: 'from',
                to: v298,
                tok: undefined /* Nothing */
                });
              sim_r.txns.push({
                kind: 'halt',
                tok: undefined /* Nothing */
                })
              sim_r.isHalt = true;
              
              return sim_r;
              }),
            soloSend: false,
            timeoutAt: undefined /* mto */,
            tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc2, ctc0],
            waitIfNotPresent: false
            }));
          const {data: [], secs: v411, time: v410, didSend: v172, from: v409 } = txn5;
          ;
          const v412 = stdlib.addressEq(v298, v409);
          const v413 = stdlib.addressEq(v315, v409);
          const v414 = v412 ? true : v413;
          stdlib.assert(v414, {
            at: 'reach standard library:200:11:dot',
            fs: ['at ./index.rsh:86:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
            msg: 'sender correct',
            who: 'Bob'
            });
          ;
          stdlib.protect(ctc1, await interact.informTimeout(), {
            at: './index.rsh:45:55:application',
            fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:86:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
            msg: 'informTimeout',
            who: 'Bob'
            });
          
          return;
          
          }
        else {
          const {data: [v368], secs: v370, time: v369, didSend: v101, from: v367 } = txn4;
          ;
          const v371 = stdlib.addressEq(v315, v367);
          stdlib.assert(v371, {
            at: './index.rsh:85:13:dot',
            fs: [],
            msg: 'sender correct',
            who: 'Bob'
            });
          const v378 = stdlib.add(v369, v300);
          const txn5 = await (ctc.recv({
            didSend: false,
            evt_cnt: 2,
            funcNum: 8,
            out_tys: [ctc0, ctc0],
            timeoutAt: ['time', v378],
            waitIfNotPresent: false
            }));
          if (txn5.didTimeout) {
            const txn6 = await (ctc.sendrecv({
              args: [v298, v299, v300, v315, v328, v352, v368, v378],
              evt_cnt: 0,
              funcNum: 9,
              lct: v369,
              onlyIf: true,
              out_tys: [],
              pay: [stdlib.checkedBigNumberify('reach standard library:200:11:decimal', stdlib.UInt_max, '0'), []],
              sim_p: (async (txn6) => {
                const sim_r = { txns: [], mapRefs: [], maps: [] };
                let sim_txn_ctr = stdlib.UInt_max;
                const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
                
                
                const {data: [], secs: v395, time: v394, didSend: v138, from: v393 } = txn6;
                
                ;
                sim_r.txns.push({
                  kind: 'from',
                  to: v315,
                  tok: undefined /* Nothing */
                  });
                sim_r.txns.push({
                  kind: 'halt',
                  tok: undefined /* Nothing */
                  })
                sim_r.isHalt = true;
                
                return sim_r;
                }),
              soloSend: false,
              timeoutAt: undefined /* mto */,
              tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc2, ctc0, ctc0],
              waitIfNotPresent: false
              }));
            const {data: [], secs: v395, time: v394, didSend: v138, from: v393 } = txn6;
            ;
            const v396 = stdlib.addressEq(v298, v393);
            const v397 = stdlib.addressEq(v315, v393);
            const v398 = v396 ? true : v397;
            stdlib.assert(v398, {
              at: 'reach standard library:200:11:dot',
              fs: ['at ./index.rsh:94:57:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
              msg: 'sender correct',
              who: 'Bob'
              });
            ;
            stdlib.protect(ctc1, await interact.informTimeout(), {
              at: './index.rsh:45:55:application',
              fs: ['at ./index.rsh:45:13:application call to [unknown function] (defined at: ./index.rsh:45:30:function exp)', 'at reach standard library:203:8:application call to "after" (defined at: ./index.rsh:44:30:function exp)', 'at ./index.rsh:94:57:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
              msg: 'informTimeout',
              who: 'Bob'
              });
            
            return;
            
            }
          else {
            const {data: [v383, v384], secs: v386, time: v385, didSend: v111, from: v382 } = txn5;
            ;
            const v387 = stdlib.addressEq(v298, v382);
            stdlib.assert(v387, {
              at: './index.rsh:93:17:dot',
              fs: [],
              msg: 'sender correct',
              who: 'Bob'
              });
            const v388 = stdlib.digest(ctc3, [v383, v384]);
            const v389 = stdlib.digestEq(v352, v388);
            stdlib.assert(v389, {
              at: 'reach standard library:69:17:application',
              fs: ['at ./index.rsh:96:26:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
              msg: null,
              who: 'Bob'
              });
            const v390 = stdlib.sub(stdlib.checkedBigNumberify('./index.rsh:8:18:decimal', stdlib.UInt_max, '4'), v368);
            const v391 = stdlib.add(v384, v390);
            const v392 = stdlib.mod(v391, stdlib.checkedBigNumberify('./index.rsh:8:34:decimal', stdlib.UInt_max, '3'));
            const cv320 = v392;
            const cv321 = v385;
            const cv328 = v328;
            
            v320 = cv320;
            v321 = cv321;
            v328 = cv328;
            
            continue;}
          
          }
        
        }
      
      }
    const v441 = stdlib.eq(v320, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '2'));
    const v444 = stdlib.mul(stdlib.checkedBigNumberify('./index.rsh:104:12:decimal', stdlib.UInt_max, '2'), v299);
    const v446 = v441 ? v298 : v315;
    ;
    return;
    }
  
  
  
  };
const _ALGO = {
  ABI: {
    impure: [],
    pure: [],
    sigs: []
    },
  appApproval: `BiAQAAFQBQkgCAcoAniAAQQDWDAmAwEAAQEAIjUAMRhBBI8qZEkiWzUBIQZbNQI2GgAXSUEAByI1BCM1BgA2GgIXNQQ2GgM2GgEXSSUMQAIsSSEHDEABOEkhBgxAAN5JIQQMQABWIQQSRCEENAESRDQESSISTDQCEhFEKGQpZFBJNQNXMCA1/4AEogVmjrAyBjQDIQtbD0Q0A1cAIDEAEjT/MQASEUSxIrIBNAMkW7III7IQNP+yB7NCA6dIIQQ0ARJENARJIhJMNAISEUQoZClkUEk1A1cAIDX/STUFSSJbNf4hBls1/YAENRoq0DT+FlA0/RZQsDIGNAMhC1sMRDT/MQASRDQDV1ggNP4WNP0WUAESRDT/NAMhBVs0AyEIWzQDVzAgNP0hDDQDIQpbCQghDRgyBjQDJFtCAsVIIQc0ARJENARJIhJMNAISEUQoZClkUEk1A1cAIDX/gATiG7OpsDIGNAMhClsPRDT/MQASNANXMCAxABIRRLEisgE0AyRbsggjshA0/7IHs0IC00mBBgxAAJdIIQc0ARJENARJIhJMNAISEUQoZClkUEk1A0lKSlcAIDX/IQVbNf4hCFs1/VcwIDX8JFs1+1dYIDX6STUFFzX5gARw7e96NPkWULAyBjQDIQpbDEQ0/DEAEkQyBjT9CDX4NP80/hZQNP0WUDT8UDT7FlA0+lA0+RZQNPgWUChLAVcAf2cpSwFXfwlnSCEENQEyBjUCQgJQSCU0ARJENARJIhJMNAISEUQoZEk1A1cwIDX/gATMmZJcsDIGNAMhDlsPRDQDVwAgMQASNP8xABIRRLEisgE0AyRbsggjshA0/7IHs0IB5kkhCQxAANBJIQwMQACISCU0ARJENARJIhJMNAISEUQoZEk1A0lKSVcAIDX/IQVbNf4hCFs1/VcwIDX8JFs1+0k1BTX6gAQ4sCMtNPpQsDIGNAMhDlsMRDT/MQASRDIGNP0INfk0/zT+FlA0/RZQNPxQNPsWUDT6UDT5FlAoSwFXAH9nKUsBV38BZ0ghBzUBMgY1AkIBayEJEkQjNAESRDQESSISTDQCEhFEKGQ1A4AEQbFATbAyBjQDIQ9bD0SxIrIBNAMhBVuyCCOyEDQDVwAgsgezQgEPSSMMQABISCM0ARJENARJIhJMNAISEUQoZEk1AyEFWzX/gASai5F0sDIGNAMhD1sMRDT/iAFGNANXACA0/zQDIQhbMQAjMgY0/0kIQgBgSIGgjQaIASYiNAESRDQESSISTDQCEhFESTUFSSJbNf8hBls1/oAErNEfwzT/FlA0/hZQsDT/iAD1MgY0/gg1/TEANP8WUDT+FlA0/RZQKEsBVwA4Z0gjNQEyBjUCQgB8Nf81/jX9Nfw1+zX6Nfk0/SMSQQAuNP40+wg1+DT5NPoWUDT7FlA0/FA0/xZQNPgWUChLAVcAYGdIJTUBMgY1AkIAObEisgEhCTT6C7III7IQNPw0+TT9IQkSTbIHs0IAADEZJRJEsSKyASKyCCOyEDIJsgkyCrIHs0IABTEZIhJEKjQBFjQCFlBnNAZBAAqABBUffHU0B1CwNABJIwgyBBJEMRYSRCNDMRkiEkRC/98iMTQSRCENMTUSRCIxNhJEIjE3EkQiNQEiNQJC/640AElKIwg1ADgHMgoSRDgQIxJEOAgSRIk=`,
  appClear: `Bg==`,
  companionInfo: null,
  extraPages: 0,
  mapDataKeys: 0,
  mapDataSize: 0,
  stateKeys: 2,
  stateSize: 136,
  unsupported: [],
  version: 10,
  warnings: []
  };
const _ETH = {
  ABI: `[
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v299",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v300",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "stateMutability": "payable",
    "type": "constructor"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "msg",
        "type": "uint256"
      }
    ],
    "name": "ReachError",
    "type": "error"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v299",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v300",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e0",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e1",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e2",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v352",
                "type": "uint256"
              }
            ],
            "internalType": "struct T10",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T11",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e4",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e5",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v368",
                "type": "uint256"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e6",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e7",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v383",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v384",
                "type": "uint256"
              }
            ],
            "internalType": "struct T15",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T16",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e8",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e9",
    "type": "event"
  },
  {
    "stateMutability": "payable",
    "type": "fallback"
  },
  {
    "inputs": [],
    "name": "_reachCreationTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentState",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      },
      {
        "internalType": "bytes",
        "name": "",
        "type": "bytes"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m1",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m2",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v352",
                "type": "uint256"
              }
            ],
            "internalType": "struct T10",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T11",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m4",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m5",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v368",
                "type": "uint256"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m6",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m7",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v383",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v384",
                "type": "uint256"
              }
            ],
            "internalType": "struct T15",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T16",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m8",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m9",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "stateMutability": "payable",
    "type": "receive"
  }
]`,
  Bytecode: `0x608060405260405162001b5538038062001b5583398101604081905262000026916200024b565b6000808055436003556040805160208082018352928152815133815284518185015284840151805182850152909301516060840152905190917fa736757a943474ef5983bb0422ab3a1e64bcd39e99635f4430c7765118231f95919081900360800190a16020820151516200009f903414600762000144565b6020808301510151620000b39043620002ab565b81526040805160808082018352600060208084018281528486018381526060808701858152338089528b860180515186525186015184528a5182526001968790554390965588518086019690965292518589015290519084015251828401528451808303909301835260a0909101909352805191926200013a92600292909101906200016e565b505050506200030f565b816200016a5760405163100960cb60e01b81526004810182905260240160405180910390fd5b5050565b8280546200017c90620002d2565b90600052602060002090601f016020900481019282620001a05760008555620001eb565b82601f10620001bb57805160ff1916838001178555620001eb565b82800160010185558215620001eb579182015b82811115620001eb578251825591602001919060010190620001ce565b50620001f9929150620001fd565b5090565b5b80821115620001f95760008155600101620001fe565b604080519081016001600160401b03811182821017156200024557634e487b7160e01b600052604160045260246000fd5b60405290565b600081830360608112156200025f57600080fd5b6200026962000214565b835181526040601f19830112156200028057600080fd5b6200028a62000214565b60208581015182526040909501518582015293810193909352509092915050565b60008219821115620002cd57634e487b7160e01b600052601160045260246000fd5b500190565b600181811c90821680620002e757607f821691505b602082108114156200030957634e487b7160e01b600052602260045260246000fd5b50919050565b611836806200031f6000396000f3fe60806040526004361061009a5760003560e01c80638e314769116100615780638e31476914610115578063980b6eac14610128578063a209ad4e1461013b578063ab53f2c61461014e578063bf2c5b2414610171578063de7369981461018457005b80631e93b0f1146100a35780632c10a159146100c75780637eea518c146100da57806383230757146100ed5780638328d4c41461010257005b366100a157005b005b3480156100af57600080fd5b506003545b6040519081526020015b60405180910390f35b6100a16100d53660046113dc565b610197565b6100a16100e83660046113dc565b61032e565b3480156100f957600080fd5b506001546100b4565b6100a16101103660046113ff565b6104ac565b6100a16101233660046113dc565b6106d9565b6100a16101363660046113dc565b610874565b6100a16101493660046113dc565b610b15565b34801561015a57600080fd5b50610163610d59565b6040516100be929190611411565b6100a161017f3660046113dc565b610df6565b6100a16101923660046113dc565b610f8d565b6101a760016000541460096110e3565b6101c1813515806101ba57506001548235145b600a6110e3565b6000808055600280546101d39061146e565b80601f01602080910402602001604051908101604052809291908181526020018280546101ff9061146e565b801561024c5780601f106102215761010080835404028352916020019161024c565b820191906000526020600020905b81548152906001019060200180831161022f57829003601f168201915b505050505080602001905181019061026491906114bf565b905061027781606001514310600b6110e3565b7f400d21ea4e4a5e28b4ae5f0f476c201fc8036473fcf7c8cd252f38698020b4f133836040516102a8929190611538565b60405180910390a16102c18160200151341460086110e3565b6102c9611295565b815181516001600160a01b039091169052602080830180518351830152604080850151845190910152825133606090910152818301805160019052514392019190915251610317908061158b565b60208201516040015261032981611108565b505050565b61033e600160005414600d6110e3565b6103588135158061035157506001548235145b600e6110e3565b60008080556002805461036a9061146e565b80601f01602080910402602001604051908101604052809291908181526020018280546103969061146e565b80156103e35780601f106103b8576101008083540402835291602001916103e3565b820191906000526020600020905b8154815290600101906020018083116103c657829003601f168201915b50505050508060200190518101906103fb91906114bf565b905061040f8160600151431015600f6110e3565b7f919263be6d51bec670ce110fb6a7df03fe323e3de4dade5355bccc6a4b06d9503383604051610440929190611538565b60405180910390a16104543415600c6110e3565b805160208201516040516001600160a01b039092169181156108fc0291906000818181858888f19350505050158015610491573d6000803e3d6000fd5b50600080805560018190556104a8906002906112ee565b5050565b6104bc60096000541460276110e3565b6104d6813515806104cf57506001548235145b60286110e3565b6000808055600280546104e89061146e565b80601f01602080910402602001604051908101604052809291908181526020018280546105149061146e565b80156105615780601f1061053657610100808354040283529160200191610561565b820191906000526020600020905b81548152906001019060200180831161054457829003601f168201915b505050505080602001905181019061057991906115a3565b905061058c8160e00151431060296110e3565b604080513381528335602080830191909152840135818301529083013560608201527f71b5093cb50f6a6c807d17b0994efe213c21a3f7fc6bd14bf50facf7ea99022e9060800160405180910390a16105e7341560246110e3565b80516105ff906001600160a01b0316331460256110e3565b6040805161064b9161062591602080870135928701359101918252602082015260400190565b6040516020818303038152906040528051906020012060001c8260a001511460266110e3565b610653611295565b815181516001600160a01b0391821690526020808401518351909101526040808401518351909101526060808401518351921691015260c082015160039061069c90600461164f565b6106aa90604086013561158b565b6106b49190611666565b6020808301805192909252815143910152608083015190516040015261032981611108565b6106e960056000541460176110e3565b610703813515806106fc57506001548235145b60186110e3565b6000808055600280546107159061146e565b80601f01602080910402602001604051908101604052809291908181526020018280546107419061146e565b801561078e5780601f106107635761010080835404028352916020019161078e565b820191906000526020600020905b81548152906001019060200180831161077157829003601f168201915b50505050508060200190518101906107a69190611688565b90506107ba8160a0015143101560196110e3565b7fbe731e9f2a129299a212b8ec3ac324fa99671cd00a5a827cbd3d4fe6d7ad541d33836040516107eb929190611538565b60405180910390a16107ff341560156110e3565b8051610833906001600160a01b031633146108295760608201516001600160a01b0316331461082c565b60015b60166110e3565b80606001516001600160a01b03166108fc82608001519081150290604051600060405180830381858888f19350505050158015610491573d6000803e3d6000fd5b610884600760005414601c6110e3565b61089e8135158061089757506001548235145b601d6110e3565b6000808055600280546108b09061146e565b80601f01602080910402602001604051908101604052809291908181526020018280546108dc9061146e565b80156109295780601f106108fe57610100808354040283529160200191610929565b820191906000526020600020905b81548152906001019060200180831161090c57829003601f168201915b5050505050806020019051810190610941919061171c565b90506109596040518060200160405280600081525090565b61096a8260c001514310601e6110e3565b7fa2ddd0bc62239facbd79cdab1df75ee0cb72af9166d4371e62852a98cb4ca19c338460405161099b9291906117ba565b60405180910390a16109af3415601a6110e3565b60608201516109ca906001600160a01b03163314601b6110e3565b60408201516109d9904361158b565b81526040805161010081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c0810182905260e081019190915282516001600160a01b0390811682526020808501518184015260408086015181850152606080870151909316928401929092526080808601519084015260a080860151908401528581013560c0840152835160e08401526009600055436001559051610aea9183910160006101008201905060018060a01b038084511683526020840151602084015260408401516040840152806060850151166060840152506080830151608083015260a083015160a083015260c083015160c083015260e083015160e083015292915050565b60405160208183030381529060405260029080519060200190610b0e92919061132b565b5050505050565b610b2560056000541460126110e3565b610b3f81351580610b3857506001548235145b60136110e3565b600080805560028054610b519061146e565b80601f0160208091040260200160405190810160405280929190818152602001828054610b7d9061146e565b8015610bca5780601f10610b9f57610100808354040283529160200191610bca565b820191906000526020600020905b815481529060010190602001808311610bad57829003601f168201915b5050505050806020019051810190610be29190611688565b9050610bfa6040518060200160405280600081525090565b610c0b8260a00151431060146110e3565b7f117ff0fc7909f539043dcba1a015e3c49852b86bcb1c87a6cfa653f771ccbdc03384604051610c3c9291906117ba565b60405180910390a1610c50341560106110e3565b8151610c68906001600160a01b0316331460116110e3565b6040820151610c77904361158b565b81526040805160e081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c081019190915282516001600160a01b039081168083526020808601518185019081526040808801518187019081526060808a015187168189019081526080808c0151818b019081528d88013560a0808d019182528d5160c0808f0191825260076000554360015589519b8c019c909c529851978a0197909752945193880193909352905190971696850196909652945190830152925191810191909152905160e082015261010001610aea565b600060606000546002808054610d6e9061146e565b80601f0160208091040260200160405190810160405280929190818152602001828054610d9a9061146e565b8015610de75780601f10610dbc57610100808354040283529160200191610de7565b820191906000526020600020905b815481529060010190602001808311610dca57829003601f168201915b50505050509050915091509091565b610e0660076000541460216110e3565b610e2081351580610e1957506001548235145b60226110e3565b600080805560028054610e329061146e565b80601f0160208091040260200160405190810160405280929190818152602001828054610e5e9061146e565b8015610eab5780601f10610e8057610100808354040283529160200191610eab565b820191906000526020600020905b815481529060010190602001808311610e8e57829003601f168201915b5050505050806020019051810190610ec3919061171c565b9050610ed78160c0015143101560236110e3565b7f3a35e33c7cbe4475e726117e3691b4a75ad6c9b28c29c59a1ef792dd449861bb3383604051610f08929190611538565b60405180910390a1610f1c3415601f6110e3565b8051610f50906001600160a01b03163314610f465760608201516001600160a01b03163314610f49565b60015b60206110e3565b805160808201516040516001600160a01b039092169181156108fc0291906000818181858888f19350505050158015610491573d6000803e3d6000fd5b610f9d600960005414602c6110e3565b610fb781351580610fb057506001548235145b602d6110e3565b600080805560028054610fc99061146e565b80601f0160208091040260200160405190810160405280929190818152602001828054610ff59061146e565b80156110425780601f1061101757610100808354040283529160200191611042565b820191906000526020600020905b81548152906001019060200180831161102557829003601f168201915b505050505080602001905181019061105a91906115a3565b905061106e8160e00151431015602e6110e3565b7f7533cfcbaea81c55f5c15df7ca9474738a32835ebe63ae177376e624bc7df0bd338360405161109f929190611538565b60405180910390a16110b33415602a6110e3565b8051610833906001600160a01b031633146110dd5760608201516001600160a01b031633146110e0565b60015b602b5b816104a85760405163100960cb60e01b81526004810182905260240160405180910390fd5b6040805160208101909152600081526020820151516001141561123057815160400151602080840151015161113d919061158b565b81526040805160c081018252600080825260208201819052918101829052606081018290526080810182905260a08101919091528251516001600160a01b039081168083528451602090810151818501908152865160409081015181870190815288516060908101518716818901908152858b01518401516080808b019182528b5160a0808d019182526005600055436001558751998a019a909a529651958801959095529251918601919091525190951690830152925191810191909152905160c082015260e0016040516020818303038152906040526002908051906020019061122a92919061132b565b50505050565b6020820151516002146112485781516060015161124c565b8151515b6001600160a01b03166108fc836000015160200151600261126d91906117e1565b6040518115909202916000818181858888f19350505050158015610491573d6000803e3d6000fd5b6040805160c0810182526000918101828152606082018390526080820183905260a082019290925290819081526020016112e960405180606001604052806000815260200160008152602001600081525090565b905290565b5080546112fa9061146e565b6000825580601f1061130a575050565b601f01602090049060005260206000209081019061132891906113af565b50565b8280546113379061146e565b90600052602060002090601f016020900481019282611359576000855561139f565b82601f1061137257805160ff191683800117855561139f565b8280016001018555821561139f579182015b8281111561139f578251825591602001919060010190611384565b506113ab9291506113af565b5090565b5b808211156113ab57600081556001016113b0565b6000604082840312156113d657600080fd5b50919050565b6000604082840312156113ee57600080fd5b6113f883836113c4565b9392505050565b6000606082840312156113d657600080fd5b82815260006020604081840152835180604085015260005b8181101561144557858101830151858201606001528201611429565b81811115611457576000606083870101525b50601f01601f191692909201606001949350505050565b600181811c9082168061148257607f821691505b602082108114156113d657634e487b7160e01b600052602260045260246000fd5b80516001600160a01b03811681146114ba57600080fd5b919050565b6000608082840312156114d157600080fd5b6040516080810181811067ffffffffffffffff8211171561150257634e487b7160e01b600052604160045260246000fd5b60405261150e836114a3565b81526020830151602082015260408301516040820152606083015160608201528091505092915050565b6001600160a01b03831681528135602080830191909152606082019083013580151580821461156657600080fd5b80604085015250509392505050565b634e487b7160e01b600052601160045260246000fd5b6000821982111561159e5761159e611575565b500190565b60006101008083850312156115b757600080fd5b6040519081019067ffffffffffffffff821181831017156115e857634e487b7160e01b600052604160045260246000fd5b816040526115f5846114a3565b81526020840151602082015260408401516040820152611617606085016114a3565b60608201526080840151608082015260a084015160a082015260c084015160c082015260e084015160e0820152809250505092915050565b60008282101561166157611661611575565b500390565b60008261168357634e487b7160e01b600052601260045260246000fd5b500690565b600060c0828403121561169a57600080fd5b60405160c0810181811067ffffffffffffffff821117156116cb57634e487b7160e01b600052604160045260246000fd5b6040526116d7836114a3565b815260208301516020820152604083015160408201526116f9606084016114a3565b60608201526080830151608082015260a083015160a08201528091505092915050565b600060e0828403121561172e57600080fd5b60405160e0810181811067ffffffffffffffff8211171561175f57634e487b7160e01b600052604160045260246000fd5b60405261176b836114a3565b8152602083015160208201526040830151604082015261178d606084016114a3565b60608201526080830151608082015260a083015160a082015260c083015160c08201528091505092915050565b6001600160a01b0383168152606081016113f8602083018480358252602090810135910152565b60008160001904831182151516156117fb576117fb611575565b50029056fea2646970667358221220846f70ea90eda4c88f8fe89012c09eaf9931210035ec13a255df945a119b7cf564736f6c634300080c0033`,
  BytecodeLen: 6997,
  Which: `oD`,
  version: 7,
  views: {
    }
  };
export const _stateSourceMap = {
  1: {
    at: './index.rsh:55:13:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  2: {
    at: 'reach standard library:202:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:63:53:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  4: {
    at: './index.rsh:105:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  5: {
    at: './index.rsh:70:17:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  6: {
    at: 'reach standard library:202:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:78:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  7: {
    at: './index.rsh:79:17:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  8: {
    at: 'reach standard library:202:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:86:55:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  9: {
    at: './index.rsh:87:17:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  10: {
    at: 'reach standard library:202:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:94:57:application call to "closeTo" (defined at: reach standard library:198:8:function exp)'],
    msg: null,
    who: 'Module'
    }
  };
export const _Connectors = {
  ALGO: _ALGO,
  ETH: _ETH
  };
export const _Participants = {
  "Alice": Alice,
  "Bob": Bob
  };
export const _APIs = {
  };
