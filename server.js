'use strict';
/**
 * 인사이더 (통 파일 버전)
 *
 * 이 파일 하나와 package.json 만 있으면 된다.
 *   로컬 실행:  npm install  →  npm start  →  http://localhost:3000
 *   Render:     Build Command `npm install`, Start Command `npm start`
 *
 * 구성 (위에서 아래로)
 *   1. 게임 로직   - 방, 역할, 질문/답변, 투표, 점수
 *   2. 화면(HTML)  - 브라우저에 그대로 내려 주는 한 장짜리 페이지
 *   3. 서버        - 소켓 이벤트를 게임 로직에 연결
 *
 * 바꾸고 싶은 값: WORDS(제시어), CFG(인원, 시간, 차례제 여부)
 */
const http = require('http');
const crypto = require('crypto');
const { Server } = require('socket.io');

// ═════════════════════════════════════════════════════════════
// 1. 게임 로직
// ═════════════════════════════════════════════════════════════
// ─────────────────────────────────────────────────────────────
// 제시어 (예/아니오 질문으로 좁혀 갈 수 있는 구체적인 명사 위주)
// 여기만 고치면 단어가 바뀐다.
// ─────────────────────────────────────────────────────────────
const WORDS = [
  // 음식
  '김치찌개', '떡볶이', '치킨', '라면', '피자', '초밥', '삼겹살', '짜장면', '아이스크림', '김밥',
  '햄버거', '순대', '붕어빵', '호떡', '마라탕', '냉면', '비빔밥', '샌드위치', '팝콘', '초콜릿',
  // 장소
  '놀이공원', '도서관', '편의점', '지하철', '목욕탕', '노래방', '영화관', '공항', '캠핑장', '수영장',
  '병원', '찜질방', '피시방', '동물원', '해수욕장', '헬스장',
  // 사물
  '우산', '냉장고', '선풍기', '안경', '칫솔', '리모컨', '에어컨', '이어폰', '보조배터리', '가위',
  '거울', '시계', '베개', '텀블러', '자전거', '캐리어', '전자레인지', '마우스', '키보드', '지갑',
  '열쇠', '라이터', '손톱깎이', '빨래건조대', '청소기',
  // 직업
  '소방관', '의사', '요리사', '경찰관', '선생님', '가수', '택배기사', '변호사', '파일럿', '개그맨',
  '마술사', '유튜버',
  // 동물
  '고양이', '펭귄', '코끼리', '카멜레온', '앵무새', '기린', '고래', '거북이', '토끼', '햄스터',
  // 상황과 행사
  '무지개', '눈사람', '태풍', '화산', '사막', '크리스마스', '생일파티', '소풍', '월드컵', '올림픽',
  '결혼식', '롤러코스터', '낙하산', '불꽃놀이', '캠프파이어', '첫눈', '방학', '월급날', '야근', '회식',
];

const CFG = {
  minPlayers: 4,
  maxPlayers: 8,
  maxRoomSize: 12, // 관전자 포함
  askMs: 5 * 60 * 1000,
  discussMs: 3 * 60 * 1000,
  voteMs: 60 * 1000,
  turnBased: true, // true: 한 명씩 차례대로 질문, false: 아무나 아무 때나 질문
};

const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const ANSWERS = { yes: '예', no: '아니오', idk: '모르겠음' };

function userError(message) {
  const e = new Error(message);
  e.userMessage = message;
  return e;
}

const clean = (s, n) =>
  String(s == null ? '' : s).replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, n);

const pick = (arr) => arr[crypto.randomInt(arr.length)];

function makeCode(exists) {
  for (let i = 0; i < 50; i++) {
    let c = '';
    for (let j = 0; j < 4; j++) c += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
    if (!exists(c)) return c;
  }
  throw userError('방 코드를 만들지 못했어요. 잠시 후 다시 시도해 주세요.');
}

class Room {
  constructor(code, onChange, cfg) {
    this.code = code;
    this.onChange = onChange || (() => {});
    this.cfg = Object.assign({}, CFG, cfg || {});
    this.players = new Map(); // token -> player
    this.hostToken = null;
    this.phase = 'lobby'; // lobby | asking | discussion | vote | result
    this.round = 0;
    this.chat = []; // 잡담 채널
    this.qa = []; // 질문과 답변 채널 (라운드마다 비움)
    this.msgSeq = 0;
    this.joinSeq = 0;
    this.usedWords = new Set();
    this.timer = null;
    this.endsAt = null;
    this.touch();
    this.resetRound();
  }

  // ── 내부 유틸 ──────────────────────────────────────────────
  touch() { this.lastActivity = Date.now(); }

  resetRound() {
    this.masterToken = null;
    this.insiderToken = null;
    this.word = null;
    this.guessedBy = null;
    this.skip = new Set();
    this.votes = new Map(); // voterToken -> targetId
    this.result = null;
    this.qOrder = []; // 질문 순서 (출제자 제외 참가자 token)
    this.turnIdx = 0;
    this.queue = []; // 출제자의 답을 기다리는 질문 id
  }

  byId(id) {
    for (const p of this.players.values()) if (p.id === id) return p;
    return null;
  }

  actives() { return [...this.players.values()].filter((p) => p.active); }
  connectedActives() { return this.actives().filter((p) => p.connected); }
  connectedCount() { return [...this.players.values()].filter((p) => p.connected).length; }

  push(msg, ch) {
    msg.id = ++this.msgSeq;
    msg.t = Date.now();
    const arr = ch === 'qa' ? this.qa : this.chat;
    arr.push(msg);
    if (arr.length > 300) arr.splice(0, arr.length - 300);
    return msg;
  }
  // ch: 'talk'(기본) | 'qa' | 'both'
  sys(text, ch) {
    if (ch === 'both') {
      this.push({ type: 'sys', text }, 'talk');
      return this.push({ type: 'sys', text }, 'qa');
    }
    return this.push({ type: 'sys', text }, ch || 'talk');
  }

  setPhase(phase, ms) {
    clearTimeout(this.timer);
    this.phase = phase;
    this.endsAt = ms ? Date.now() + ms : null;
    this.timer = ms ? setTimeout(() => this.onTimer(phase), ms) : null;
  }

  onTimer(phase) {
    if (this.phase !== phase) return;
    if (phase === 'asking') {
      this.finish({ winner: 'none', reason: 'timeout' });
    } else if (phase === 'discussion') {
      this.toVote();
    } else if (phase === 'vote') {
      this.resolveVote();
    }
    this.onChange(this);
  }

  ensureHost() {
    const host = this.players.get(this.hostToken);
    if (host && host.connected) return;
    for (const p of this.players.values()) {
      if (p.connected) { this.hostToken = p.token; return; }
    }
  }

  dispose() { clearTimeout(this.timer); this.timer = null; }

  // ── 입장과 퇴장 ─────────────────────────────────────────────
  join(token, rawName) {
    this.touch();
    let p = this.players.get(token);
    if (p) {
      p.connected = true;
      return p;
    }
    const base = clean(rawName, 10);
    if (!base) throw userError('이름을 입력해 주세요.');
    if (this.players.size >= this.cfg.maxRoomSize) throw userError('방이 가득 찼어요.');
    let name = base;
    let n = 2;
    const names = new Set([...this.players.values()].map((x) => x.name));
    while (names.has(name)) name = `${base}${n++}`;
    p = {
      token,
      id: crypto.randomBytes(4).toString('hex'),
      name,
      connected: true,
      active: this.phase === 'lobby' || this.phase === 'result',
      ready: false,
      score: 0,
      masterCount: 0,
      order: ++this.joinSeq,
      sid: null,
    };
    this.players.set(token, p);
    if (!this.hostToken) this.hostToken = token;
    this.sys(`${name}님이 들어왔어요.`);
    return p;
  }

  setConnected(token, connected) {
    const p = this.players.get(token);
    if (!p) return;
    p.connected = connected;
    if (!connected) p.sid = null;
    this.touch();
    this.afterPresenceChange();
  }

  // 접속이 끊긴 사람을 기다리다 막히지 않도록 진행 조건을 다시 확인한다.
  afterPresenceChange() {
    if (this.phase === 'asking') {
      this.normalizeTurn();
    } else if (this.phase === 'discussion') {
      const act = this.connectedActives();
      if (act.length && act.every((p) => this.skip.has(p.token))) this.toVote();
    } else if (this.phase === 'vote') {
      const act = this.connectedActives();
      if (act.length && act.every((p) => this.votes.has(p.token))) this.resolveVote();
    }
  }

  leave(token) {
    const p = this.players.get(token);
    if (!p) return;
    this.touch();
    if (this.phase === 'lobby' || this.phase === 'result') {
      this.players.delete(token);
      this.sys(`${p.name}님이 나갔어요.`);
    } else {
      p.connected = false;
      p.sid = null;
      this.sys(`${p.name}님의 접속이 끊겼어요.`);
      this.afterPresenceChange();
    }
    this.ensureHost();
  }

  kick(token, targetId) {
    if (token !== this.hostToken) throw userError('방장만 내보낼 수 있어요.');
    if (this.phase !== 'lobby' && this.phase !== 'result') throw userError('라운드 중에는 내보낼 수 없어요.');
    const t = this.byId(targetId);
    if (!t || t.token === token) throw userError('내보낼 수 없는 대상이에요.');
    this.players.delete(t.token);
    this.sys(`${t.name}님이 방에서 나갔어요.`);
    return t.sid;
  }

  // ── 라운드 진행 ─────────────────────────────────────────────
  // ── 게임 준비 ───────────────────────────────────────────────
  setReady(token, flag) {
    const p = this.players.get(token);
    if (!p) return;
    if (this.phase !== 'lobby' && this.phase !== 'result') throw userError('라운드가 끝난 뒤에 준비할 수 있어요.');
    p.ready = !!flag;
    this.touch();
  }

  readyCount() {
    return [...this.players.values()].filter((p) => p.connected && p.ready).length;
  }

  // ── 라운드 진행 ─────────────────────────────────────────────
  // 준비를 누른 사람이 min명 이상이면 누구든 시작할 수 있다. 준비한 사람만 참가자가 된다.
  start(token) {
    if (!this.players.has(token)) throw userError('방 정보를 찾을 수 없어요.');
    if (this.phase !== 'lobby' && this.phase !== 'result') throw userError('이미 진행 중이에요.');
    const n = this.readyCount();
    if (n < this.cfg.minPlayers) throw userError(`게임 준비를 누른 사람이 ${this.cfg.minPlayers}명 이상이어야 해요.`);
    if (n > this.cfg.maxPlayers) {
      throw userError(`최대 ${this.cfg.maxPlayers}명까지 할 수 있어요. 일부는 준비를 취소해 주세요.`);
    }
    for (const p of this.players.values()) p.active = p.connected && p.ready;

    const actives = this.actives();
    // 출제자는 맡은 횟수가 적은 사람부터 (동률이면 먼저 들어온 사람)
    const master = [...actives].sort((a, b) => a.masterCount - b.masterCount || a.order - b.order)[0];
    const insider = pick(actives.filter((p) => p !== master));

    if (this.usedWords.size >= WORDS.length) this.usedWords.clear();
    const word = pick(WORDS.filter((w) => !this.usedWords.has(w)));
    this.usedWords.add(word);

    this.resetRound();
    this.qa = [];
    this.round += 1;
    master.masterCount += 1;
    this.masterToken = master.token;
    this.insiderToken = insider.token;
    this.word = word;

    // 질문 순서는 무작위로 섞는다 (인사이더가 항상 같은 순번이 되지 않도록)
    const askers = actives.filter((p) => p !== master).map((p) => p.token);
    for (let i = askers.length - 1; i > 0; i--) {
      const j = crypto.randomInt(i + 1);
      [askers[i], askers[j]] = [askers[j], askers[i]];
    }
    this.qOrder = askers;
    this.turnIdx = 0;

    this.setPhase('asking', this.cfg.askMs);
    this.normalizeTurn();
    this.sys(`${this.round}번째 라운드를 시작해요. 출제자는 ${master.name}님이에요.`, 'both');
    this.touch();
  }

  cancel(token) {
    if (token !== this.hostToken) throw userError('방장만 중단할 수 있어요.');
    if (this.phase === 'lobby') return;
    clearTimeout(this.timer);
    this.timer = null;
    this.resetRound();
    this.phase = 'lobby';
    this.endsAt = null;
    for (const p of this.players.values()) p.active = true;
    this.sys('방장이 라운드를 중단했어요.');
    this.touch();
  }

  chatMsg(token, rawText) {
    const p = this.players.get(token);
    if (!p) return;
    const text = clean(rawText, 200);
    if (!text) return;
    if (this.phase === 'asking' && token === this.masterToken) {
      throw userError('출제자는 예, 아니오, 모르겠음 버튼으로만 답할 수 있어요.');
    }
    const spectating = ['asking', 'discussion', 'vote'].includes(this.phase) && !p.active;
    this.push({ type: 'chat', pid: p.id, name: p.name, text, spec: spectating }, 'talk');
    this.touch();
  }

  // 차례 계산: 접속이 끊긴 사람은 건너뛴다 (답을 기다리는 질문이 있으면 건드리지 않는다)
  normalizeTurn() {
    if (!this.cfg.turnBased || this.phase !== 'asking' || this.queue.length) return;
    const n = this.qOrder.length;
    for (let i = 0; i < n; i++) {
      const p = this.players.get(this.qOrder[this.turnIdx]);
      if (p && p.connected) return;
      this.turnIdx = (this.turnIdx + 1) % n;
    }
  }

  advanceTurn() {
    if (!this.cfg.turnBased || !this.qOrder.length) return;
    this.turnIdx = (this.turnIdx + 1) % this.qOrder.length;
    this.normalizeTurn();
  }

  currentAsker() {
    return this.cfg.turnBased ? this.players.get(this.qOrder[this.turnIdx]) || null : null;
  }

  ask(token, rawText) {
    if (this.phase !== 'asking') throw userError('지금은 질문할 수 없어요.');
    const p = this.players.get(token);
    if (!p || !p.active) throw userError('관전 중에는 질문할 수 없어요.');
    if (token === this.masterToken) throw userError('출제자는 질문할 수 없어요.');
    const text = clean(rawText, 120);
    if (!text) return;
    if (this.cfg.turnBased) {
      this.normalizeTurn();
      if (this.qOrder[this.turnIdx] !== token) throw userError('아직 내 차례가 아니에요.');
      if (this.queue.length) throw userError('출제자가 답할 때까지 기다려 주세요.');
    } else if (this.queue.length >= 10) {
      throw userError('답을 기다리는 질문이 너무 많아요.');
    }
    const m = this.push({ type: 'question', pid: p.id, name: p.name, text, ans: null }, 'qa');
    this.queue.push(m.id);
    this.touch();
  }

  pass(token) {
    if (this.phase !== 'asking') throw userError('지금은 패스할 수 없어요.');
    if (!this.cfg.turnBased) throw userError('패스는 차례제에서만 쓸 수 있어요.');
    this.normalizeTurn();
    if (this.qOrder[this.turnIdx] !== token) throw userError('내 차례에만 패스할 수 있어요.');
    if (this.queue.length) throw userError('이미 질문을 보냈어요.');
    const p = this.players.get(token);
    this.sys(`${p.name}님이 패스했어요.`, 'qa');
    this.advanceTurn();
    this.touch();
  }

  answer(token, kind) {
    if (this.phase !== 'asking') throw userError('지금은 답할 수 없어요.');
    if (token !== this.masterToken) throw userError('출제자만 답할 수 있어요.');
    if (!ANSWERS[kind]) throw userError('알 수 없는 답이에요.');
    if (!this.queue.length) throw userError('답할 질문이 아직 없어요.');
    const qid = this.queue.shift();
    const q = this.qa.find((x) => x.id === qid);
    if (q) q.ans = { kind, text: ANSWERS[kind] };
    this.advanceTurn();
    this.touch();
  }

  guess(token, rawText) {
    if (this.phase !== 'asking') throw userError('지금은 정답을 말할 수 없어요.');
    const p = this.players.get(token);
    if (!p || !p.active) throw userError('관전 중에는 참여할 수 없어요.');
    if (token === this.masterToken) throw userError('출제자는 정답을 말할 수 없어요.');
    const text = clean(rawText, 20);
    if (!text) return;
    if (this.qa.some((m) => m.type === 'guess' && m.pid === p.id && m.status === 'pending')) {
      throw userError('이전 정답 시도를 출제자가 판정할 때까지 기다려 주세요.');
    }
    this.push({ type: 'guess', pid: p.id, name: p.name, text, status: 'pending' }, 'qa');
    this.touch();
  }

  judge(token, msgId, correct) {
    if (this.phase !== 'asking') throw userError('지금은 판정할 수 없어요.');
    if (token !== this.masterToken) throw userError('출제자만 판정할 수 있어요.');
    const m = this.qa.find((x) => x.id === msgId && x.type === 'guess');
    if (!m || m.status !== 'pending') throw userError('판정할 정답 시도가 없어요.');
    if (!correct) {
      m.status = 'wrong';
      this.touch();
      return;
    }
    m.status = 'correct';
    for (const x of this.qa) if (x.type === 'guess' && x.status === 'pending') x.status = 'void';
    this.queue = [];
    this.guessedBy = m.name;
    this.sys(`정답이에요. ${m.name}님이 맞혔어요. 이제 인사이더를 찾아 보세요.`, 'both');
    this.setPhase('discussion', this.cfg.discussMs);
    this.touch();
  }

  skipDiscuss(token) {
    if (this.phase !== 'discussion') throw userError('지금은 투표로 넘어갈 수 없어요.');
    const p = this.players.get(token);
    if (!p || !p.active) throw userError('관전 중에는 참여할 수 없어요.');
    this.skip.add(token);
    this.touch();
    this.afterPresenceChange();
  }

  toVote() {
    this.votes = new Map();
    this.setPhase('vote', this.cfg.voteMs);
    this.sys('투표 시간이에요. 인사이더로 의심되는 사람을 골라 주세요.');
  }

  castVote(token, targetId) {
    if (this.phase !== 'vote') throw userError('지금은 투표할 수 없어요.');
    const p = this.players.get(token);
    if (!p || !p.active) throw userError('관전 중에는 투표할 수 없어요.');
    const t = this.byId(targetId);
    if (!t || !t.active) throw userError('투표할 수 없는 대상이에요.');
    if (t.token === token) throw userError('자기 자신에게는 투표할 수 없어요.');
    this.votes.set(token, t.id);
    this.touch();
    this.afterPresenceChange();
  }

  resolveVote() {
    const tally = new Map();
    for (const id of this.votes.values()) tally.set(id, (tally.get(id) || 0) + 1);
    const max = Math.max(0, ...tally.values());
    const leaders = [...tally].filter(([, n]) => n === max).map(([id]) => id);
    const insider = this.players.get(this.insiderToken);
    const caught = max > 0 && leaders.length === 1 && leaders[0] === insider.id;
    this.finish({ winner: caught ? 'crew' : 'insider', reason: caught ? 'caught' : (leaders.length > 1 || max === 0 ? 'tie' : 'missed') });
  }

  finish({ winner, reason }) {
    const insider = this.players.get(this.insiderToken);
    const master = this.players.get(this.masterToken);
    const votes = [...this.votes].map(([voter, targetId]) => ({
      from: this.players.get(voter) ? this.players.get(voter).name : '?',
      to: this.byId(targetId) ? this.byId(targetId).name : '?',
    }));
    const tally = {};
    for (const v of votes) tally[v.to] = (tally[v.to] || 0) + 1;

    if (winner === 'insider') {
      insider.score += 2;
    } else if (winner === 'crew') {
      for (const p of this.actives()) if (p.token !== insider.token) p.score += 1;
    }

    this.result = {
      winner, // 'insider' | 'crew' | 'none'
      reason, // 'caught' | 'missed' | 'tie' | 'timeout'
      insiderId: insider.id,
      insiderName: insider.name,
      masterName: master.name,
      guessedBy: this.guessedBy,
      word: this.word,
      votes,
      tally,
    };
    this.setPhase('result', 0);
    const msg = {
      crew: `인사이더 ${insider.name}님을 찾아냈어요.`,
      insider: `인사이더 ${insider.name}님의 승리예요.`,
      none: `시간이 끝났어요. 인사이더는 ${insider.name}님이었어요.`,
    }[winner];
    this.sys(msg, 'both');
  }

  turnView() {
    const asker = this.currentAsker();
    return {
      turnBased: this.cfg.turnBased,
      askerId: asker ? asker.id : null,
      order: this.cfg.turnBased
        ? this.qOrder.map((t) => this.players.get(t)).filter(Boolean).map((p) => ({ id: p.id, name: p.name }))
        : [],
      waiting: this.queue.length > 0,
    };
  }

  // ── 플레이어별 화면 상태 ─────────────────────────────────────
  view(token) {
    const me = this.players.get(token);
    const inRound = this.phase !== 'lobby';
    let role = null;
    if (me && inRound) {
      if (!me.active) role = 'spectator';
      else if (token === this.masterToken) role = 'master';
      else if (token === this.insiderToken) role = 'insider';
      else role = 'commoner';
    }
    const wordPublic = ['discussion', 'vote', 'result'].includes(this.phase);
    const canSeeWord = wordPublic || role === 'master' || role === 'insider';

    const online = [...this.players.values()].filter((p) => p.connected).length;

    return {
      code: this.code,
      phase: this.phase,
      round: this.round,
      endsAt: this.endsAt,
      serverNow: Date.now(),
      cfg: { min: this.cfg.minPlayers, max: this.cfg.maxPlayers },
      online,
      readyCount: this.readyCount(),
      me: {
        id: me ? me.id : null,
        name: me ? me.name : '',
        role,
        isHost: token === this.hostToken,
        ready: !!(me && me.ready),
        word: canSeeWord ? this.word : null,
        myVote: this.phase === 'vote' && this.votes.has(token) ? this.votes.get(token) : null,
        skipped: this.phase === 'discussion' && this.skip.has(token),
      },
      players: [...this.players.values()]
        .sort((a, b) => a.order - b.order)
        .map((p) => ({
          id: p.id,
          name: p.name,
          connected: p.connected,
          active: p.active,
          ready: p.ready,
          score: p.score,
          isHost: p.token === this.hostToken,
          isMaster: inRound && p.token === this.masterToken,
          voted: this.phase === 'vote' && this.votes.has(p.token),
          skipped: this.phase === 'discussion' && this.skip.has(p.token),
        })),
      guessedBy: this.guessedBy,
      result: this.phase === 'result' ? this.result : null,
      turn: this.phase === 'asking' ? this.turnView() : null,
      qa: this.qa.slice(-80),
      chat: this.chat.slice(-120),
    };
  }
}

// ═════════════════════════════════════════════════════════════
// 2. 화면 (HTML)
// ═════════════════════════════════════════════════════════════
const HTML = `<!doctype html>
<html lang="ko">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="color-scheme" content="light dark">
<title>인사이더</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Do+Hyeon&family=IBM+Plex+Sans+KR:wght@400;500;600&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #ECEAF3;
    --panel: #F8F7FC;
    --ink: #1E1A3C;
    --muted: #625E80;
    --line: #CFCBE0;
    --primary: #3A35C8;
    --primary-ink: #FFFFFF;
    --signal: #D42A63;
    --signal-ink: #FFFFFF;
    --ok: #17725B;
    --display: "Do Hyeon", "Apple SD Gothic Neo", "Malgun Gothic", sans-serif;
    --body: "IBM Plex Sans KR", "Apple SD Gothic Neo", "Malgun Gothic", system-ui, sans-serif;
    color-scheme: light;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg: #15132A;
      --panel: #1F1C3B;
      --ink: #EDEBFA;
      --muted: #A6A2C6;
      --line: #36325C;
      --primary: #9591FF;
      --primary-ink: #15132A;
      --signal: #FF6B96;
      --signal-ink: #2B0B1A;
      --ok: #55D6AC;
      color-scheme: dark;
    }
  }
  * { box-sizing: border-box; }
  html { -webkit-text-size-adjust: 100%; }
  body {
    margin: 0;
    background: var(--bg);
    color: var(--ink);
    font: 400 16px/1.55 var(--body);
    padding: env(safe-area-inset-top) env(safe-area-inset-right) env(safe-area-inset-bottom) env(safe-area-inset-left);
  }
  [hidden] { display: none !important; }
  h1, h2, h3 { font-family: var(--display); font-weight: 400; margin: 0; line-height: 1.2; }
  button, input { font: inherit; color: inherit; }
  :focus-visible { outline: 3px solid var(--primary); outline-offset: 2px; }

  .btn {
    min-height: 44px; padding: .6rem 1rem; border-radius: 10px;
    border: 1px solid var(--line); background: var(--panel); cursor: pointer;
  }
  .btn:hover:not(:disabled) { border-color: var(--primary); }
  .btn:disabled { opacity: .5; cursor: not-allowed; }
  .btn.primary { background: var(--primary); border-color: var(--primary); color: var(--primary-ink); font-weight: 600; }
  .btn.danger { border-color: var(--signal); color: var(--signal); }
  .btn.small { min-height: 32px; padding: .2rem .65rem; font-size: .875rem; }
  .btn.link { border: 0; background: none; color: var(--muted); text-decoration: underline; min-height: 32px; padding: .2rem .4rem; }

  input[type=text] {
    width: 100%; min-height: 44px; padding: .55rem .8rem; border-radius: 10px;
    border: 1px solid var(--line); background: var(--panel);
  }
  input[type=text]::placeholder { color: var(--muted); }

  /* ───── 입장 화면 ───── */
  #landing { max-width: 420px; margin: 0 auto; padding: 12vh 1.25rem 2rem; }
  #landing h1 { font-size: 3.4rem; letter-spacing: -.01em; }
  #landing .lead { margin: .4rem 0 2rem; color: var(--muted); }
  .field { display: grid; gap: .35rem; margin-bottom: 1.1rem; }
  .field label { font-weight: 600; font-size: .95rem; }
  .row { display: flex; gap: .6rem; }
  .row > * { flex: 1; }
  .divider { margin: 1.6rem 0 1.2rem; border: 0; border-top: 1px solid var(--line); }
  #serverNote { margin-top: 1rem; color: var(--muted); font-size: .9rem; min-height: 1.4em; }
  #code-input { text-transform: uppercase; letter-spacing: .2em; text-align: center; font-weight: 600; }

  /* ───── 방 화면 ───── */
  #roomView { max-width: 1040px; margin: 0 auto; padding: .75rem; }
  .top {
    display: flex; flex-wrap: wrap; align-items: center; gap: .5rem .9rem;
    padding: .25rem .25rem .75rem;
  }
  .top .room { display: flex; align-items: center; gap: .5rem; }
  .top .room b { font-family: var(--display); font-weight: 400; font-size: 1.6rem; letter-spacing: .12em; }
  .top .phase { display: flex; align-items: baseline; gap: .6rem; margin-left: auto; }
  #phaseLabel { font-weight: 600; }
  #timer { font-family: var(--display); font-size: 1.7rem; min-width: 3.2ch; text-align: right; font-variant-numeric: tabular-nums; }
  #timer.low { color: var(--signal); }
  .top-actions { display: flex; gap: .25rem; width: 100%; justify-content: flex-end; }

  .layout { display: grid; gap: .75rem; }
  @media (min-width: 900px) {
    .layout { grid-template-columns: 360px 1fr; align-items: start; }
    .top-actions { width: auto; }
    #chat { height: clamp(200px, calc(100vh - 660px), 420px) !important; max-height: none !important; }
  }
  .panel { background: var(--panel); border: 1px solid var(--line); border-radius: 14px; padding: .85rem; }
  .side { display: grid; gap: .75rem; }

  #players { list-style: none; margin: 0; padding: 0; display: grid; gap: .1rem; }
  #players li {
    display: grid; grid-template-columns: auto 1fr auto; gap: .5rem; align-items: center;
    padding: .35rem .15rem; border-bottom: 1px solid var(--line);
  }
  #players li:last-child { border-bottom: 0; }
  .dot { width: .6rem; height: .6rem; border-radius: 50%; background: var(--ok); }
  .dot.off { background: transparent; border: 2px solid var(--muted); }
  .pname { display: flex; flex-wrap: wrap; align-items: center; gap: .3rem; min-width: 0; overflow-wrap: anywhere; }
  .pname.me { font-weight: 600; }
  .badge { font-size: .75rem; padding: 0 .45rem; border-radius: 99px; border: 1px solid var(--line); color: var(--muted); }
  .badge.strong { border-color: var(--primary); color: var(--primary); }
  .score { font-variant-numeric: tabular-nums; font-weight: 600; }
  .right { display: flex; align-items: center; gap: .5rem; }

  /* 내 카드: 누르고 있는 동안만 보인다 */
  .card {
    display: block; width: 100%; min-height: 136px; padding: 1rem 1.1rem; border: 0; border-radius: 16px;
    text-align: left; cursor: pointer; background: var(--ink); color: var(--bg);
    user-select: none; -webkit-user-select: none; -webkit-touch-callout: none; touch-action: none;
    transition: transform .12s ease;
  }
  .card:active, .card.open { transform: scale(.985); }
  .card .face { display: none; }
  .card.open .cover { display: none; }
  .card.open .face { display: block; }
  .cover-title { display: block; font-family: var(--display); font-size: 1.6rem; }
  .cover-hint { display: block; margin-top: .2rem; opacity: .8; font-size: .92rem; }
  .face-role { display: block; font-weight: 600; opacity: .9; }
  .face-word { display: block; font-family: var(--display); font-size: 2.6rem; line-height: 1.15; margin: .15rem 0 .25rem; overflow-wrap: anywhere; }
  .face-note { display: block; font-size: .92rem; opacity: .92; }
  .card[data-role=insider].open { background: var(--signal); color: var(--signal-ink); }
  .card[data-role=master].open { background: var(--primary); color: var(--primary-ink); }

  #stage { display: grid; gap: .6rem; }
  #stage p { margin: 0; }
  #stage h2 { font-size: 1.5rem; }
  #stage .muted, .muted { color: var(--muted); }
  details summary { cursor: pointer; font-weight: 600; }
  details ul { margin: .5rem 0 0; padding-left: 1.2rem; color: var(--muted); font-size: .92rem; }

  .vote-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(110px, 1fr)); gap: .5rem; }
  .vote-btn { min-height: 52px; }
  .vote-btn[aria-pressed=true] { background: var(--primary); border-color: var(--primary); color: var(--primary-ink); font-weight: 600; }
  .votes { margin: 0; padding-left: 1.1rem; color: var(--muted); font-size: .92rem; }
  .facts { display: grid; gap: .15rem; }
  .facts b { font-weight: 600; }

  /* ───── 채팅 ───── */
  .talk { display: grid; gap: .6rem; }
  /* 잡담: 평평하고 조용하게 */
  .talk-panel h3 { font: 600 .95rem var(--body); color: var(--muted); margin-bottom: .4rem; }
  #chat {
    height: 30vh; min-height: 180px; max-height: 360px; overflow-y: auto;
    display: flex; flex-direction: column; gap: .3rem; padding: .1rem 0 .5rem;
  }

  /* 질문과 답변: 게임의 중심이라 색, 테두리, 말풍선 모양으로 잡담과 확실히 구분한다 */
  .qa {
    border: 2px solid var(--primary); border-radius: 14px; overflow: hidden;
    background: var(--panel);
    background: color-mix(in srgb, var(--primary) 7%, var(--panel));
  }
  .qa-head { display: flex; align-items: baseline; gap: .6rem; padding: .55rem .85rem; background: var(--primary); color: var(--primary-ink); }
  .qa-head h2 { font-size: 1.25rem; }
  .qa-head span { font-size: .85rem; opacity: .92; }
  .qa-turn { display: flex; flex-wrap: wrap; align-items: center; gap: .4rem .75rem; padding: .55rem .85rem; border-bottom: 1px solid var(--line); }
  .turn-text { font-weight: 600; }
  .turn-order { display: flex; flex-wrap: wrap; gap: .3rem; }
  .turnchip { font-size: .8rem; padding: 0 .55rem; border-radius: 99px; border: 1px solid var(--primary); color: var(--primary); }
  .turnchip.current { background: var(--primary); color: var(--primary-ink); font-weight: 600; }
  .qa-log { height: 230px; overflow-y: auto; padding: .7rem .85rem; display: flex; flex-direction: column; gap: .6rem; }
  .q { display: grid; gap: .25rem; }
  .q-bubble {
    justify-self: start; max-width: 92%; padding: .35rem .8rem .35rem .6rem; overflow-wrap: anywhere;
    background: var(--panel); border: 1.5px solid var(--primary); border-radius: 3px 14px 14px 14px;
  }
  .qtag { display: inline-block; margin-right: .4rem; padding: 0 .4rem; border-radius: 4px; background: var(--primary); color: var(--primary-ink); font-family: var(--display); }
  .a-line { justify-self: end; }
  .a-line.wait { color: var(--muted); font-size: .85rem; }
  .a-chip {
    display: inline-block; min-width: 4.5rem; text-align: center; padding: .1rem .9rem;
    border-radius: 99px; border: 2px solid currentColor; background: var(--panel);
    font-family: var(--display); font-size: 1.15rem;
  }
  .a-chip.yes { color: var(--ok); }
  .a-chip.no { color: var(--signal); }
  .a-chip.idk { color: var(--muted); }
  .qa-composer { display: grid; gap: .5rem; padding: .7rem .85rem; border-top: 1px solid var(--line); }
  .qa-composer form { display: grid; gap: .5rem; }
  .qa-composer .btns { display: flex; gap: .5rem; }
  .qa-composer .btns .btn { flex: 1; }
  .qa-composer .guess-form { grid-template-columns: 1fr auto; }
  .qa .msg.guess { background: var(--panel); }
  .msg { overflow-wrap: anywhere; }
  .msg .who { font-weight: 600; margin-right: .4rem; }
  .msg.me .who { color: var(--primary); }
  .msg.sys { color: var(--muted); font-size: .9rem; text-align: center; padding: .15rem 0; }
  .msg.answer { padding: .15rem .6rem; border-left: 3px solid var(--line); }
  .chip { display: inline-block; padding: 0 .55rem; border-radius: 99px; font-weight: 600; border: 1px solid currentColor; }
  .chip.yes { color: var(--ok); }
  .chip.no { color: var(--signal); }
  .chip.idk { color: var(--muted); }
  .msg.guess { padding: .4rem .6rem; border: 1px solid var(--primary); border-radius: 10px; }
  .msg.guess .state { margin-left: .4rem; font-size: .85rem; color: var(--muted); }
  .msg.guess.correct { border-color: var(--ok); }
  .msg.guess.correct .state { color: var(--ok); font-weight: 600; }
  .msg.guess.wrong { opacity: .75; }
  .judge { display: flex; gap: .4rem; margin-top: .4rem; }

  #composer form { display: grid; gap: .5rem; }
  #composer .btns { display: flex; gap: .5rem; }
  #composer .btns .btn { flex: 1; }
  .answers { display: grid; grid-template-columns: repeat(3, 1fr); gap: .5rem; }
  .answers .btn { min-height: 56px; font-weight: 600; font-size: 1.05rem; }
  .notice { margin: 0; color: var(--muted); font-size: .92rem; }

  #toast {
    position: fixed; left: 50%; bottom: calc(1rem + env(safe-area-inset-bottom)); transform: translateX(-50%);
    max-width: min(92vw, 420px); padding: .6rem 1rem; border-radius: 10px;
    background: var(--ink); color: var(--bg); box-shadow: 0 6px 24px rgba(0,0,0,.25);
    opacity: 0; pointer-events: none; transition: opacity .15s ease; z-index: 10;
  }
  #toast.show { opacity: 1; }
  #conn { margin: 0 0 .5rem; padding: .4rem .75rem; border-radius: 10px; background: var(--signal); color: var(--signal-ink); font-size: .92rem; }

  @media (prefers-reduced-motion: reduce) {
    .card, #toast { transition: none; }
  }
</style>
</head>
<body>

<main id="landing">
  <h1>인사이더</h1>
  <p class="lead">정답을 아는 척하지 않는 사람이 이긴다. 4~8명이 함께 해요.</p>

  <div class="field">
    <label for="name-input">이름</label>
    <input id="name-input" type="text" maxlength="10" autocomplete="nickname" placeholder="최대 10자">
  </div>
  <button class="btn primary" id="create-btn" style="width:100%">방 만들기</button>

  <hr class="divider">

  <div class="field">
    <label for="code-input">방 코드</label>
    <div class="row">
      <input id="code-input" type="text" maxlength="4" inputmode="text" autocapitalize="characters" autocomplete="off" placeholder="ABCD">
      <button class="btn" id="join-btn">입장하기</button>
    </div>
  </div>
  <p id="serverNote" role="status"></p>
</main>

<div id="roomView" hidden>
  <p id="conn" role="status" hidden>연결이 끊겼어요. 다시 연결하는 중이에요.</p>
  <header class="top">
    <div class="room">
      <span class="muted">방 코드</span>
      <b id="code"></b>
      <button class="btn small" id="copy-btn">링크 복사</button>
    </div>
    <div class="phase">
      <span id="phaseLabel"></span>
      <span id="timer" aria-live="off"></span>
    </div>
    <div class="top-actions">
      <button class="btn link" id="cancel-btn" hidden>라운드 중단</button>
      <button class="btn link" id="leave-btn">나가기</button>
    </div>
  </header>

  <div class="layout">
    <section class="side">
      <div class="panel"><ul id="players" aria-label="참가자"></ul></div>
      <button class="card" id="card" hidden aria-label="내 카드. 누르고 있는 동안 내용이 보여요.">
        <span class="cover">
          <span class="cover-title">내 카드</span>
          <span class="cover-hint">꾹 누르고 있으면 보여요</span>
        </span>
        <span class="face">
          <span class="face-role" id="faceRole"></span>
          <span class="face-word" id="faceWord"></span>
          <span class="face-note" id="faceNote"></span>
        </span>
      </button>
      <div class="panel" id="stage"></div>
    </section>

    <section class="talk">
      <div class="qa" id="qaPanel" hidden>
        <div class="qa-head"><h2>질문과 답변</h2><span>출제자에게 묻고 답을 듣는 곳</span></div>
        <div class="qa-turn" id="qaTurn" hidden></div>
        <div class="qa-log" id="qaLog" role="log" aria-live="polite" aria-label="질문과 답변"></div>
        <div class="qa-composer" id="qaComposer" hidden></div>
      </div>
      <div class="panel talk-panel">
        <h3>잡담</h3>
        <div id="chat" role="log" aria-live="polite" aria-label="잡담"></div>
        <div id="composer"></div>
      </div>
    </section>
  </div>
</div>

<div id="toast" role="status" aria-live="polite"></div>

<script src="/socket.io/socket.io.js"></script>
<script>
(() => {
  'use strict';
  const $ = (s) => document.querySelector(s);
  const socket = io();

  const PHASE = { lobby: '대기실', asking: '질문 시간', discussion: '인사이더 토론', vote: '투표', result: '결과' };
  const KEY_TOKEN = 'insider.token';
  const KEY_NAME = 'insider.name';
  const KEY_SESSION = 'insider.session';

  let state = null;
  let offset = 0;
  const rendered = new Map(); // 컨테이너별 마지막 렌더 키 (입력 중인 폼을 지우지 않기 위함)

  // ── 유틸 ────────────────────────────────────────────────────
  function el(tag, props, ...kids) {
    const e = document.createElement(tag);
    for (const [k, v] of Object.entries(props || {})) {
      if (v == null || v === false) continue;
      if (k === 'class') e.className = v;
      else if (k === 'text') e.textContent = v;
      else if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
      else if (v === true) e.setAttribute(k, '');
      else e.setAttribute(k, v);
    }
    for (const kid of kids.flat()) {
      if (kid == null || kid === false) continue;
      e.append(kid.nodeType ? kid : document.createTextNode(String(kid)));
    }
    return e;
  }

  function fill(node, key, build) {
    if (rendered.get(node) === key) return false;
    rendered.set(node, key);
    node.replaceChildren(...build().flat(Infinity).filter((x) => x != null && x !== false));
    return true;
  }

  let toastTimer;
  function toast(msg) {
    const t = $('#toast');
    t.textContent = msg;
    t.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => t.classList.remove('show'), 2800);
  }

  function getToken() {
    let t = sessionStorage.getItem(KEY_TOKEN);
    if (!t) {
      t = (crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2) + Date.now().toString(36) + Math.random().toString(36).slice(2));
      sessionStorage.setItem(KEY_TOKEN, t);
    }
    return t;
  }
  const getSession = () => { try { return JSON.parse(sessionStorage.getItem(KEY_SESSION) || 'null'); } catch (_) { return null; } };
  const setSession = (code, name) => sessionStorage.setItem(KEY_SESSION, JSON.stringify({ code, name }));
  const clearSession = () => sessionStorage.removeItem(KEY_SESSION);

  function send(event, data, done) {
    socket.emit(event, data || {}, (res) => {
      if (res && res.ok === false) toast(res.error || '문제가 생겼어요.');
      else if (done) done(res);
    });
  }

  function showLanding() {
    state = null;
    $('#roomView').hidden = true;
    $('#landing').hidden = false;
    if (location.hash) history.replaceState(null, '', location.pathname);
  }

  // ── 입장 화면 ───────────────────────────────────────────────
  const nameInput = $('#name-input');
  const codeInput = $('#code-input');
  nameInput.value = localStorage.getItem(KEY_NAME) || '';
  const hashCode = location.hash.replace('#', '').trim().toUpperCase();
  if (hashCode) codeInput.value = hashCode.slice(0, 4);

  function enter(event, extra) {
    const name = nameInput.value.trim();
    if (!name) { toast('이름을 입력해 주세요.'); nameInput.focus(); return; }
    localStorage.setItem(KEY_NAME, name);
    send(event, Object.assign({ token: getToken(), name }, extra), (res) => {
      setSession(res.code, name);
      history.replaceState(null, '', '#' + res.code);
    });
  }
  $('#create-btn').addEventListener('click', () => enter('create'));
  $('#join-btn').addEventListener('click', () => {
    const code = codeInput.value.trim().toUpperCase();
    if (code.length !== 4) { toast('방 코드 4자리를 입력해 주세요.'); codeInput.focus(); return; }
    enter('join', { code });
  });
  [nameInput, codeInput].forEach((i) => i.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') (codeInput.value.trim() ? $('#join-btn') : $('#create-btn')).click();
  }));

  // ── 연결 상태 ───────────────────────────────────────────────
  function setServerNote() {
    const note = $('#serverNote');
    if (socket.connected) note.textContent = '';
    else note.textContent = '서버에 연결하는 중이에요. 무료 서버는 처음에 켜지는 데 1분 가까이 걸릴 수 있어요.';
    $('#conn').hidden = socket.connected || !state;
  }
  socket.on('connect', () => {
    setServerNote();
    let ss = getSession();
    const linkCode = location.hash.replace('#', '').trim().toUpperCase();
    if (ss && linkCode && linkCode !== ss.code) { clearSession(); ss = null; }
    if (ss) {
      socket.emit('join', { code: ss.code, token: getToken(), name: ss.name }, (res) => {
        if (!res || !res.ok) { clearSession(); showLanding(); if (res && res.error) toast(res.error); }
      });
    }
  });
  socket.on('disconnect', setServerNote);
  socket.on('connect_error', setServerNote);
  setServerNote();

  socket.on('kicked', () => { clearSession(); showLanding(); toast('방장이 방에서 내보냈어요.'); });
  socket.on('state', (s) => {
    state = s;
    offset = s.serverNow - Date.now();
    render();
  });

  // ── 헤더 버튼 ───────────────────────────────────────────────
  $('#copy-btn').addEventListener('click', async () => {
    const url = location.origin + '/#' + state.code;
    try { await navigator.clipboard.writeText(url); toast('초대 링크를 복사했어요.'); }
    catch (_) { toast('복사하지 못했어요. 방 코드를 알려 주세요: ' + state.code); }
  });
  $('#leave-btn').addEventListener('click', () => {
    if (!confirm('방에서 나갈까요?')) return;
    send('leave', {}, () => { clearSession(); showLanding(); });
  });
  $('#cancel-btn').addEventListener('click', () => {
    if (confirm('이번 라운드를 중단하고 대기실로 돌아갈까요?')) send('cancel');
  });

  // ── 내 카드: 누르는 동안만 보이게 ────────────────────────────
  const card = $('#card');
  const openCard = () => card.classList.add('open');
  const closeCard = () => card.classList.remove('open');
  card.addEventListener('pointerdown', (e) => { e.preventDefault(); openCard(); });
  ['pointerup', 'pointercancel', 'pointerleave'].forEach((ev) => card.addEventListener(ev, closeCard));
  card.addEventListener('keydown', (e) => { if (e.key === ' ' || e.key === 'Enter') { e.preventDefault(); openCard(); } });
  card.addEventListener('keyup', (e) => { if (e.key === ' ' || e.key === 'Enter') closeCard(); });
  card.addEventListener('contextmenu', (e) => e.preventDefault());
  window.addEventListener('blur', closeCard);
  document.addEventListener('visibilitychange', () => { if (document.hidden) closeCard(); });

  function cardInfo(s) {
    const m = s.me;
    switch (m.role) {
      case 'master': return { role: '출제자', word: m.word, note: '제시어를 알고 있어요. 예, 아니오, 모르겠음으로만 답하세요.' };
      case 'insider': return { role: '인사이더', word: m.word, note: '정체를 숨기고, 정답이 나오도록 티 나지 않게 이끄세요.' };
      case 'commoner': return { role: '일반인', word: m.word, note: m.word ? '' : '제시어를 몰라요. 질문으로 좁혀 가세요.' };
      default: return { role: '관전 중', word: m.word, note: '다음 라운드부터 함께해요.' };
    }
  }

  // ── 렌더 ───────────────────────────────────────────────────
  function render() {
    const s = state;
    if (!s) return;
    $('#landing').hidden = true;
    $('#roomView').hidden = false;
    $('#conn').hidden = socket.connected;
    $('#code').textContent = s.code;
    $('#phaseLabel').textContent = PHASE[s.phase] + (s.round && s.phase !== 'lobby' ? \` (\${s.round}라운드)\` : '');
    $('#cancel-btn').hidden = !(s.me.isHost && ['asking', 'discussion', 'vote'].includes(s.phase));
    renderPlayers(s);
    renderCard(s);
    renderStage(s);
    renderQa(s);
    renderChat(s);
    renderComposer(s);
    tick();
  }

  function renderPlayers(s) {
    const canKick = s.me.isHost && (s.phase === 'lobby' || s.phase === 'result');
    const key = JSON.stringify([s.players, s.phase, s.me.id, canKick]);
    fill($('#players'), key, () => s.players.map((p) => {
      const isMe = p.id === s.me.id;
      const badges = [];
      if (p.isHost) badges.push(el('span', { class: 'badge strong', text: '방장' }));
      if (p.isMaster) badges.push(el('span', { class: 'badge strong', text: '출제자' }));
      if ((s.phase === 'lobby' || s.phase === 'result') && p.ready) badges.push(el('span', { class: 'badge strong', text: '준비' }));
      if (s.phase !== 'lobby' && !p.active) badges.push(el('span', { class: 'badge', text: '관전' }));
      if (p.voted) badges.push(el('span', { class: 'badge', text: '투표 완료' }));
      if (p.skipped) badges.push(el('span', { class: 'badge', text: '토론 마침' }));
      if (!p.connected) badges.push(el('span', { class: 'badge', text: '접속 끊김' }));
      const right = el('span', { class: 'right' },
        el('span', { class: 'score', text: \`\${p.score}점\` }),
        canKick && !isMe
          ? el('button', { class: 'btn small', text: '내보내기', onclick: () => { if (confirm(\`\${p.name}님을 내보낼까요?\`)) send('kick', { id: p.id }); } })
          : null);
      return el('li', {},
        el('span', { class: 'dot' + (p.connected ? '' : ' off'), 'aria-hidden': 'true' }),
        el('span', { class: 'pname' + (isMe ? ' me' : '') }, p.name + (isMe ? ' (나)' : ''), badges),
        right);
    }));
  }

  function renderCard(s) {
    card.hidden = s.phase === 'lobby';
    if (card.hidden) { closeCard(); return; }
    const info = cardInfo(s);
    $('#faceRole').textContent = info.role;
    $('#faceWord').textContent = info.word || '';
    $('#faceNote').textContent = info.note;
    card.dataset.role = s.me.role || '';
  }

  function renderStage(s) {
    const online = s.players.filter((p) => p.active && p.connected);
    const key = JSON.stringify([s.phase, s.me.role, s.me.isHost, s.me.skipped, s.me.myVote, s.online, s.cfg, s.readyCount, s.me.ready,
      s.guessedBy, s.result, online.length, s.players.map((p) => [p.id, p.voted, p.skipped, p.active])]);
    fill($('#stage'), key, () => {
      switch (s.phase) {
        case 'lobby': return stageLobby(s);
        case 'asking': return stageAsking(s);
        case 'discussion': return stageDiscussion(s, online);
        case 'vote': return stageVote(s, online);
        default: return stageResult(s);
      }
    });
  }

  // 게임 준비를 누른 사람이 최소 인원 이상이면 누구에게나 시작 버튼이 나타난다
  function readyBlock(s, startLabel) {
    const n = s.readyCount;
    const canStart = n >= s.cfg.min && n <= s.cfg.max;
    return [
      el('p', { text: \`게임 준비를 누른 사람은 \${n}명이에요. \${s.cfg.min}명 이상 준비하면 누구든 시작할 수 있어요.\` }),
      el('button', {
        class: 'btn' + (!s.me.ready && !canStart ? ' primary' : ''), 'aria-pressed': String(s.me.ready),
        text: s.me.ready ? '준비 취소' : '게임 준비',
        onclick: () => send('ready', { ready: !s.me.ready }),
      }),
      canStart ? el('button', { class: 'btn primary', text: startLabel, onclick: () => send('start') }) : null,
      canStart && !s.me.ready ? el('p', { class: 'muted', text: '준비하지 않은 사람은 이번 라운드를 관전해요.' }) : null,
      n > s.cfg.max ? el('p', { class: 'muted', text: \`최대 \${s.cfg.max}명이에요. 일부는 준비를 취소해 주세요.\` }) : null,
    ];
  }

  function stageLobby(s) {
    return [
      el('h2', { text: '대기실' }),
      readyBlock(s, '게임 시작'),
      el('details', {},
        el('summary', { text: '게임 방법' }),
        el('ul', {},
          el('li', { text: '게임 준비를 누른 사람만 참가해요. 4~8명이 준비하면 누구든 시작할 수 있어요.' }),
          el('li', { text: '출제자와 인사이더는 제시어를 알아요. 출제자는 누구인지 공개돼요.' }),
          el('li', { text: '일반인과 인사이더는 한 명씩 차례대로 출제자에게 질문해요. 출제자는 예, 아니오, 모르겠음 버튼으로만 답하고, 답이 나오면 다음 사람 차례예요.' }),
          el('li', { text: '정답은 차례와 상관없이 언제든 말할 수 있고 출제자가 판정해요. 5분 안에 못 맞히면 모두 패배해요.' }),
          el('li', { text: '정답이 나오면 인사이더를 투표로 찾아요. 찾으면 일반 진영이 1점씩, 못 찾거나 동점이면 인사이더가 2점을 얻어요.' }))),
    ];
  }

  function stageAsking(s) {
    const tips = {
      master: '질문이 오면 예, 아니오, 모르겠음 버튼으로 답해 주세요. 정답 시도가 오면 질문과 답변 칸에서 판정해요.',
      insider: '제시어를 알고 있어요. 들키지 않게 질문으로 정답 쪽을 이끄세요.',
      commoner: '내 차례에 예 또는 아니오로 답할 수 있는 질문을 하세요. 정답을 알면 차례와 상관없이 말할 수 있어요.',
      spectator: '관전 중이에요. 다음 라운드부터 함께해요.',
    };
    return [el('h2', { text: '질문 시간' }), el('p', { text: tips[s.me.role] || '' })];
  }

  function stageDiscussion(s, online) {
    const done = online.filter((p) => p.skipped).length;
    const canAct = s.me.role && s.me.role !== 'spectator';
    return [
      el('h2', { text: '인사이더를 찾아요' }),
      el('p', { text: \`\${s.guessedBy}님이 정답을 맞혔어요. 누가 정답으로 이끌었는지 이야기해 보세요.\` }),
      canAct
        ? el('button', {
            class: 'btn', disabled: s.me.skipped, onclick: () => send('skipDiscuss'),
            text: s.me.skipped ? \`다른 사람을 기다리는 중 (\${done}/\${online.length})\` : \`투표하러 가기 (\${done}/\${online.length})\`,
          })
        : null,
    ];
  }

  function stageVote(s, online) {
    const voted = s.players.filter((p) => p.voted).length;
    const canVote = s.me.role && s.me.role !== 'spectator';
    const targets = s.players.filter((p) => p.active && p.id !== s.me.id);
    return [
      el('h2', { text: '인사이더는 누구일까요' }),
      el('p', { class: 'muted', text: \`\${voted}/\${online.length}명이 투표했어요. 투표는 마감 전까지 바꿀 수 있어요.\` }),
      canVote
        ? el('div', { class: 'vote-grid' }, targets.map((p) =>
            el('button', { class: 'btn vote-btn', text: p.name, 'aria-pressed': String(s.me.myVote === p.id), onclick: () => send('vote', { target: p.id }) })))
        : el('p', { class: 'muted', text: '관전 중에는 투표할 수 없어요.' }),
    ];
  }

  function stageResult(s) {
    const r = s.result;
    if (!r) return [];
    const title = { crew: '인사이더를 찾았어요', insider: '인사이더의 승리예요', none: '시간 초과, 모두 패배' }[r.winner];
    const why = { caught: '', tie: '동점이거나 표가 없어서 인사이더가 이겼어요.', missed: '엉뚱한 사람을 지목했어요.', timeout: '5분 안에 정답이 나오지 않았어요.' }[r.reason];
    const lines = [
      el('div', { class: 'facts' },
        el('span', {}, '인사이더: ', el('b', { text: r.insiderName })),
        el('span', {}, '제시어: ', el('b', { text: r.word })),
        el('span', {}, '출제자: ', el('b', { text: r.masterName })),
        r.guessedBy ? el('span', {}, '맞힌 사람: ', el('b', { text: r.guessedBy })) : null),
    ];
    return [
      el('h2', { text: title }),
      why ? el('p', { class: 'muted', text: why }) : null,
      lines,
      r.votes.length
        ? el('ul', { class: 'votes' }, r.votes.map((v) => el('li', { text: \`\${v.from}님이 \${v.to}님을 지목\` })))
        : null,
      el('hr', { class: 'divider' }),
      readyBlock(s, '다음 라운드 시작'),
    ];
  }

  // ── 질문과 답변 (게임의 중심 채널) ────────────────────────────
  let wasMyTurn = false;
  const qaRef = {}; // 질문 입력 영역의 요소들 (입력 중인 글자를 지우지 않으려고 한 번만 만든다)

  function renderQa(s) {
    const panel = $('#qaPanel');
    panel.hidden = s.phase === 'lobby';
    if (panel.hidden) { wasMyTurn = false; return; }
    renderTurn(s);
    renderQaLog(s);
    renderQaComposer(s);
  }

  function renderTurn(s) {
    const box = $('#qaTurn');
    const t = s.turn;
    if (!t || !t.turnBased) { box.hidden = true; wasMyTurn = false; return; }
    box.hidden = false;
    const mine = t.askerId === s.me.id;
    const asker = t.order.find((o) => o.id === t.askerId);
    const who = asker ? asker.name : '';
    fill(box, JSON.stringify([t, s.me.id]), () => {
      let text;
      if (t.waiting) text = mine ? '출제자의 답을 기다리는 중이에요.' : \`\${who}님의 질문에 출제자가 답하는 중이에요.\`;
      else text = mine ? '내 차례예요. 질문해 주세요.' : \`\${who}님의 질문 차례예요.\`;
      return [
        el('span', { class: 'turn-text', text }),
        el('span', { class: 'turn-order', 'aria-label': '질문 순서' },
          t.order.map((o) => el('span', { class: 'turnchip' + (o.id === t.askerId ? ' current' : ''), text: o.name }))),
      ];
    });
    const myTurnNow = mine && !t.waiting;
    if (myTurnNow && !wasMyTurn) toast('내 차례예요. 질문해 주세요.');
    wasMyTurn = myTurnNow;
  }

  function renderQaLog(s) {
    const log = $('#qaLog');
    const isMaster = s.me.role === 'master' && s.phase === 'asking';
    const key = s.qa.map((m) => m.id + (m.status || '') + (m.ans ? m.ans.kind : '')).join(',') + '|' + isMaster;
    const nearBottom = log.scrollHeight - log.scrollTop - log.clientHeight < 80;
    const first = !rendered.has(log);
    const changed = fill(log, key, () => s.qa.map((m) => qaNode(m, isMaster)));
    if (changed && (nearBottom || first)) log.scrollTop = log.scrollHeight;
  }

  function qaNode(m, isMaster) {
    if (m.type === 'sys') return el('div', { class: 'msg sys', text: m.text });
    if (m.type === 'question') {
      return el('div', { class: 'q' },
        el('div', { class: 'q-bubble' },
          el('span', { class: 'qtag', text: 'Q' }), el('span', { class: 'who', text: m.name }), el('span', { text: m.text })),
        m.ans
          ? el('div', { class: 'a-line' }, el('span', { class: \`a-chip \${m.ans.kind}\`, text: m.ans.text }))
          : el('div', { class: 'a-line wait', text: '답변 대기 중' }));
    }
    const label = { pending: '판정 중', wrong: '오답', correct: '정답', void: '무효' }[m.status];
    return el('div', { class: \`msg guess \${m.status}\` },
      el('span', { class: 'who', text: \`\${m.name}님의 정답 시도\` }),
      el('span', { text: m.text }),
      el('span', { class: 'state', text: label }),
      isMaster && m.status === 'pending'
        ? el('div', { class: 'judge' },
            el('button', { class: 'btn small primary', text: '정답', onclick: () => send('judge', { id: m.id, correct: true }) }),
            el('button', { class: 'btn small', text: '오답', onclick: () => send('judge', { id: m.id, correct: false }) }))
        : null);
  }

  function renderQaComposer(s) {
    const box = $('#qaComposer');
    if (s.phase !== 'asking') { box.hidden = true; rendered.delete(box); return; }
    box.hidden = false;
    const mode = s.me.role === 'master' ? 'master' : s.me.role === 'spectator' ? 'watch' : 'ask';
    fill(box, mode, () => buildQaComposer(mode));
    updateQaComposer(s, mode);
  }

  function buildQaComposer(mode) {
    if (mode === 'watch') return [el('p', { class: 'notice', text: '관전 중에는 질문과 답변을 볼 수만 있어요.' })];
    qaRef.hint = el('p', { class: 'notice' });
    if (mode === 'master') {
      qaRef.answerBtns = [['yes', '예'], ['no', '아니오'], ['idk', '모르겠음']].map(([kind, text]) =>
        el('button', { class: 'btn', text, onclick: () => send('answer', { kind }) }));
      return [el('div', { class: 'answers' }, qaRef.answerBtns), qaRef.hint];
    }
    qaRef.qInput = el('input', { type: 'text', maxlength: '120', autocomplete: 'off', enterkeyhint: 'send', 'aria-label': '질문' });
    qaRef.askBtn = el('button', { class: 'btn primary', type: 'submit', text: '질문하기' });
    qaRef.passBtn = el('button', { class: 'btn', type: 'button', text: '패스', onclick: () => send('pass') });
    const qForm = el('form', {
      onsubmit: (e) => {
        e.preventDefault();
        const text = qaRef.qInput.value.trim();
        if (text) send('ask', { text }, () => { qaRef.qInput.value = ''; });
      },
    }, qaRef.qInput, el('div', { class: 'btns' }, qaRef.askBtn, qaRef.passBtn));
    qaRef.gInput = el('input', { type: 'text', maxlength: '20', autocomplete: 'off', placeholder: '정답을 알겠다면 여기에 (20자까지)', 'aria-label': '정답' });
    const gForm = el('form', {
      class: 'guess-form',
      onsubmit: (e) => {
        e.preventDefault();
        const text = qaRef.gInput.value.trim();
        if (text) send('guess', { text }, () => { qaRef.gInput.value = ''; });
      },
    }, qaRef.gInput, el('button', { class: 'btn', type: 'submit', text: '정답 말하기' }));
    return [qForm, gForm, qaRef.hint];
  }

  function updateQaComposer(s, mode) {
    const t = s.turn || { turnBased: true, waiting: false, askerId: null, order: [] };
    if (mode === 'master') {
      qaRef.answerBtns.forEach((b) => { b.disabled = !t.waiting; });
      qaRef.hint.textContent = t.waiting ? '위 질문에 답해 주세요.' : '다음 질문이 올 때까지 기다려 주세요.';
    } else if (mode === 'ask') {
      const mine = t.askerId === s.me.id;
      const can = t.turnBased ? mine && !t.waiting : true;
      const asker = t.order.find((o) => o.id === t.askerId);
      qaRef.qInput.disabled = !can;
      qaRef.askBtn.disabled = !can;
      qaRef.passBtn.hidden = !t.turnBased;
      qaRef.passBtn.disabled = !can;
      qaRef.qInput.placeholder = can ? '예 또는 아니오로 답할 수 있는 질문'
        : t.waiting ? '출제자의 답을 기다리는 중이에요' : \`\${asker ? asker.name : ''}님 차례예요\`;
      qaRef.hint.textContent = '정답은 차례와 상관없이 언제든 말할 수 있어요. 출제자가 판정해요.';
    }
  }

  // ── 잡담 ────────────────────────────────────────────────────
  function renderChat(s) {
    const chat = $('#chat');
    const key = s.chat.map((m) => m.id).join(',') + '|' + s.me.id;
    const nearBottom = chat.scrollHeight - chat.scrollTop - chat.clientHeight < 80;
    const first = !rendered.has(chat);
    const changed = fill(chat, key, () => s.chat.map((m) => talkNode(m, s)));
    if (changed && (nearBottom || first)) chat.scrollTop = chat.scrollHeight;
  }

  function talkNode(m, s) {
    if (m.type === 'sys') return el('div', { class: 'msg sys', text: m.text });
    return el('div', { class: 'msg' + (m.pid === s.me.id ? ' me' : '') },
      el('span', { class: 'who', text: m.name + (m.spec ? ' (관전)' : '') }), el('span', { text: m.text }));
  }

  function renderComposer(s) {
    const locked = s.phase === 'asking' && s.me.role === 'master';
    fill($('#composer'), String(locked), () => {
      if (locked) return [el('p', { class: 'notice', text: '출제자는 질문 시간에 잡담을 보낼 수 없어요. 질문에는 버튼으로 답해 주세요.' })];
      const input = el('input', { type: 'text', maxlength: '200', autocomplete: 'off', enterkeyhint: 'send', placeholder: '잡담', 'aria-label': '잡담 메시지' });
      return [el('form', {
        onsubmit: (e) => {
          e.preventDefault();
          const text = input.value.trim();
          if (text) send('chat', { text }, () => { input.value = ''; });
          input.focus();
        },
      }, input, el('button', { class: 'btn', type: 'submit', text: '보내기' }))];
    });
  }

  // 남은 시간은 서버 시각 기준으로 계산한다
  function tick() {
    const t = $('#timer');
    if (!state || !state.endsAt) { t.textContent = ''; t.classList.remove('low'); return; }
    const sec = Math.max(0, Math.ceil((state.endsAt - (Date.now() + offset)) / 1000));
    t.textContent = \`\${Math.floor(sec / 60)}:\${String(sec % 60).padStart(2, '0')}\`;
    t.classList.toggle('low', sec <= 30);
  }
  setInterval(tick, 250);
})();
</script>
</body>
</html>
`;

// ═════════════════════════════════════════════════════════════
// 3. 서버
// ═════════════════════════════════════════════════════════════
const server = http.createServer((req, res) => {
  const url = String(req.url || '/').split('?')[0];
  if (url === '/' || url === '/index.html') {
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
    return res.end(HTML);
  }
  if (url === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
    return res.end('ok');
  }
  if (url === '/favicon.ico') {
    res.writeHead(204);
    return res.end();
  }
  res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
  return res.end('not found');
});
const io = new Server(server, { pingInterval: 10000, pingTimeout: 15000 });

const rooms = new Map(); // code -> Room

// 방 상태가 바뀔 때마다 접속 중인 모든 사람에게 "자기 시점"의 화면을 보낸다.
function broadcast(room) {
  room.ensureHost();
  for (const p of room.players.values()) {
    if (p.connected && p.sid) io.to(p.sid).emit('state', room.view(p.token));
  }
}

function newRoom() {
  const code = makeCode((c) => rooms.has(c));
  const room = new Room(code, broadcast);
  rooms.set(code, room);
  return room;
}

const validToken = (t) => typeof t === 'string' && t.length >= 8 && t.length <= 80;

function attach(socket, room, token, name) {
  const p = room.join(token, name);
  p.sid = socket.id;
  p.connected = true;
  socket.data.code = room.code;
  socket.data.token = token;
  broadcast(room);
}

function run(cb, fn) {
  try {
    const result = fn();
    if (typeof cb === 'function') cb(Object.assign({ ok: true }, result || {}));
  } catch (e) {
    if (!e.userMessage) console.error(e);
    if (typeof cb === 'function') cb({ ok: false, error: e.userMessage || '문제가 생겼어요. 다시 시도해 주세요.' });
  }
}

io.on('connection', (socket) => {
  socket.data = {};

  socket.on('create', (d, cb) =>
    run(cb, () => {
      d = d || {};
      if (!validToken(d.token)) throw userError('잘못된 요청이에요.');
      const room = newRoom();
      try {
        attach(socket, room, d.token, d.name);
      } catch (e) {
        rooms.delete(room.code);
        room.dispose();
        throw e;
      }
      return { code: room.code };
    })
  );

  socket.on('join', (d, cb) =>
    run(cb, () => {
      d = d || {};
      if (!validToken(d.token)) throw userError('잘못된 요청이에요.');
      const room = rooms.get(String(d.code || '').trim().toUpperCase());
      if (!room) throw userError('없는 방이에요. 방 코드를 다시 확인해 주세요.');
      attach(socket, room, d.token, d.name);
      return { code: room.code };
    })
  );

  const actions = {
    ready: (r, t, d) => r.setReady(t, d.ready === true),
    start: (r, t) => r.start(t),
    cancel: (r, t) => r.cancel(t),
    chat: (r, t, d) => r.chatMsg(t, d.text),
    ask: (r, t, d) => r.ask(t, d.text),
    pass: (r, t) => r.pass(t),
    answer: (r, t, d) => r.answer(t, d.kind),
    guess: (r, t, d) => r.guess(t, d.text),
    judge: (r, t, d) => r.judge(t, d.id, d.correct === true),
    skipDiscuss: (r, t) => r.skipDiscuss(t),
    vote: (r, t, d) => r.castVote(t, d.target),
    kick: (r, t, d) => {
      const sid = r.kick(t, d.id);
      if (sid) io.to(sid).emit('kicked');
    },
    leave: (r, t) => {
      r.leave(t);
      socket.data = {};
    },
  };

  for (const [event, fn] of Object.entries(actions)) {
    socket.on(event, (d, cb) =>
      run(cb, () => {
        const { code, token } = socket.data || {};
        const room = rooms.get(code);
        if (!room || !room.players.has(token)) throw userError('방 정보를 찾을 수 없어요. 새로고침해 주세요.');
        fn(room, token, d || {});
        room.touch();
        broadcast(room);
      })
    );
  }

  socket.on('disconnect', () => {
    const { code, token } = socket.data || {};
    const room = rooms.get(code);
    const p = room && room.players.get(token);
    // 같은 사람이 새 탭/새로고침으로 다시 붙은 경우에는 건드리지 않는다.
    if (p && p.sid === socket.id) {
      room.setConnected(token, false);
      room.ensureHost();
      broadcast(room);
    }
  });
});

// 오래 비어 있는 방 정리 (무료 인스턴스 메모리 보호)
setInterval(() => {
  const now = Date.now();
  for (const [code, room] of rooms) {
    if (room.connectedCount() === 0 && now - room.lastActivity > 30 * 60 * 1000) {
      room.dispose();
      rooms.delete(code);
    }
  }
}, 5 * 60 * 1000).unref();

// 직접 실행했을 때만 포트를 연다 (테스트에서 불러올 때는 열지 않는다)
if (require.main === module) {
  const PORT = process.env.PORT || 3000;
  server.listen(PORT, () => console.log(`insider listening on :${PORT}`));
}

module.exports = { Room, WORDS, CFG, HTML, server, io, rooms };
