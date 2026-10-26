// @ts-nocheck
import React, { useState, useEffect, useRef, useMemo } from 'react';
import {
  QrCode,
  Users,
  UserCheck,
  Shield,
  LogIn,
  LogOut,
  Plus,
  Trash2,
  Printer,
  Download,
  Camera,
  CheckCircle2,
  XCircle,
  AlertTriangle,
  Search,
  ChevronRight,
  ArrowLeft,
  RefreshCw,
  Upload,
  FileSpreadsheet,
  KeyRound,
  Layers,
  Sparkles,
  Clock,
  MapPin,
  Award,
  Eye,
  Copy,
  Check,
  ScanLine,
  UserPlus,
  Building2,
  Mail,
  Phone,
  SlidersHorizontal,
  Smartphone,
  Globe,
  Terminal,
  Cloud
} from 'lucide-react';
import { initializeApp } from 'firebase/app';
import {
  getAuth,
  signInAnonymously,
  signInWithCustomToken,
  onAuthStateChanged
} from 'firebase/auth';
import {
  getFirestore,
  doc,
  setDoc,
  onSnapshot,
  collection
} from 'firebase/firestore';

// ============================================================================
// FIREBASE INITIALIZATION (WITH SAFE FALLBACK)
// ============================================================================
let app = null;
let auth = null;
let db = null;
const appId = typeof __app_id !== 'undefined' ? __app_id : 'hackathon-qr-manager-2026';

try {
  if (typeof __firebase_config !== 'undefined' && __firebase_config) {
    const firebaseConfig = JSON.parse(__firebase_config);
    app = initializeApp(firebaseConfig);
    auth = getAuth(app);
    db = getFirestore(app);
  }
} catch (err) {
  console.warn('Firebase initialization skipped or running in local mode:', err);
}

// ============================================================================
// REAL ISO/IEC 18004 QR CODE MATRIX GENERATOR (PURE JS, ZERO EXTERNAL DEPS)
// Supports Byte Mode Version 2-L (25x25) & Version 3-L (29x29)
// Generates 100% genuinely scannable QR codes for cameras & jsQR
// ============================================================================
const QRGenerator = (() => {
  // GF(256) exponent & log tables for Reed-Solomon (primitive polynomial 0x11d)
  const EXP = new Uint8Array(512);
  const LOG = new Uint8Array(256);
  let x = 1;
  for (let i = 0; i < 255; i++) {
    EXP[i] = x;
    LOG[x] = i;
    x <<= 1;
    if (x & 0x100) x ^= 0x11d;
  }
  for (let i = 255; i < 512; i++) {
    EXP[i] = EXP[i - 255];
  }

  function gfMul(a, b) {
    if (a === 0 || b === 0) return 0;
    return EXP[LOG[a] + LOG[b]];
  }

  function rsGeneratorPoly(degree) {
    let poly = new Uint8Array([1]);
    for (let i = 0; i < degree; i++) {
      const next = new Uint8Array(poly.length + 1);
      const factor = EXP[i];
      for (let j = 0; j < poly.length; j++) {
        next[j] ^= poly[j];
        next[j + 1] ^= gfMul(poly[j], factor);
      }
      poly = next;
    }
    return poly;
  }

  function rsEncode(data, ecLen) {
    const gen = rsGeneratorPoly(ecLen);
    const msg = new Uint8Array(data.length + ecLen);
    msg.set(data, 0);
    for (let i = 0; i < data.length; i++) {
      const coef = msg[i];
      if (coef !== 0) {
        for (let j = 0; j < gen.length; j++) {
          msg[i + j] ^= gfMul(gen[j], coef);
        }
      }
    }
    return msg.slice(data.length);
  }

  function createMatrix(text) {
    const bytes = new TextEncoder().encode(text);
    // Select Version 2-L (up to 32 bytes) or Version 3-L (up to 53 bytes) or Version 4-L (up to 78 bytes)
    let version = 2;
    let size = 25;
    let dataCapacity = 34;
    let ecCodewords = 10;
    let alignmentCoords = [6, 18];

    if (bytes.length > 32 && bytes.length <= 53) {
      version = 3;
      size = 29;
      dataCapacity = 55;
      ecCodewords = 15;
      alignmentCoords = [6, 22];
    } else if (bytes.length > 53) {
      version = 4;
      size = 33;
      dataCapacity = 80;
      ecCodewords = 20;
      alignmentCoords = [6, 26];
    }

    const payloadBytes = bytes.slice(0, dataCapacity - 2);

    // Build bit stream: Byte Mode (0100) + 8-bit length + bytes + terminator
    const bits = [];
    const pushBits = (val, len) => {
      for (let i = len - 1; i >= 0; i--) {
        bits.push((val >> i) & 1);
      }
    };

    pushBits(0b0100, 4); // Byte mode indicator
    pushBits(payloadBytes.length, 8);
    for (let i = 0; i < payloadBytes.length; i++) {
      pushBits(payloadBytes[i], 8);
    }
    // Terminator (up to 4 zeros)
    const maxBits = dataCapacity * 8;
    const termLen = Math.min(4, maxBits - bits.length);
    pushBits(0, termLen);
    while (bits.length % 8 !== 0) bits.push(0);

    const dataWords = new Uint8Array(dataCapacity);
    for (let i = 0; i < bits.length / 8; i++) {
      let b = 0;
      for (let j = 0; j < 8; j++) {
        b = (b << 1) | bits[i * 8 + j];
      }
      dataWords[i] = b;
    }
    // Pad bytes 0xEC, 0x11
    let padToggle = true;
    for (let i = bits.length / 8; i < dataCapacity; i++) {
      dataWords[i] = padToggle ? 0xec : 0x11;
      padToggle = !padToggle;
    }

    const ecWords = rsEncode(dataWords, ecCodewords);
    const allWords = new Uint8Array(dataWords.length + ecWords.length);
    allWords.set(dataWords, 0);
    allWords.set(ecWords, dataWords.length);

    const grid = Array.from({ length: size }, () => new Int8Array(size).fill(-1));
    const reserved = Array.from({ length: size }, () => new Uint8Array(size).fill(0));

    const setModule = (r, c, val, isReserved = true) => {
      if (r >= 0 && r < size && c >= 0 && c < size) {
        grid[r][c] = val ? 1 : 0;
        if (isReserved) reserved[r][c] = 1;
      }
    };

    // Finder patterns
    const drawFinder = (row, col) => {
      for (let r = -1; r <= 7; r++) {
        for (let c = -1; c <= 7; c++) {
          const rr = row + r;
          const cc = col + c;
          if (rr < 0 || rr >= size || cc < 0 || cc >= size) continue;
          const inOuter = r >= 0 && r <= 6 && c >= 0 && c <= 6;
          const inInner = r >= 2 && r <= 4 && c >= 2 && c <= 4;
          const onBorder = r === 0 || r === 6 || c === 0 || c === 6;
          setModule(rr, cc, (inOuter && onBorder) || inInner ? 1 : 0, true);
        }
      }
    };

    drawFinder(0, 0);
    drawFinder(0, size - 7);
    drawFinder(size - 7, 0);

    // Alignment pattern
    const ar = alignmentCoords[1];
    const ac = alignmentCoords[1];
    for (let r = -2; r <= 2; r++) {
      for (let c = -2; c <= 2; c++) {
        const isDark = Math.max(Math.abs(r), Math.abs(c)) !== 1;
        setModule(ar + r, ac + c, isDark ? 1 : 0, true);
      }
    }

    // Timing patterns
    for (let i = 8; i < size - 8; i++) {
      if (!reserved[6][i]) setModule(6, i, i % 2 === 0 ? 1 : 0, true);
      if (!reserved[i][6]) setModule(i, 6, i % 2 === 0 ? 1 : 0, true);
    }

    // Dark module & reserve format info areas
    setModule(size - 8, 8, 1, true);
    for (let i = 0; i < 9; i++) {
      if (!reserved[8][i]) reserved[8][i] = 1;
      if (!reserved[i][8]) reserved[i][8] = 1;
    }
    for (let i = 0; i < 8; i++) {
      if (!reserved[8][size - 1 - i]) reserved[8][size - 1 - i] = 1;
      if (!reserved[size - 1 - i][8]) reserved[size - 1 - i][8] = 1;
    }

    // Place data bits in upward/downward 2-column zig-zag
    const fullBits = [];
    for (let i = 0; i < allWords.length; i++) {
      for (let b = 7; b >= 0; b--) {
        fullBits.push((allWords[i] >> b) & 1);
      }
    }

    let bitIdx = 0;
    let upward = true;
    for (let col = size - 1; col > 0; col -= 2) {
      if (col === 6) col--; // Skip vertical timing line
      for (let i = 0; i < size; i++) {
        const row = upward ? size - 1 - i : i;
        for (let d = 0; d < 2; d++) {
          const c = col - d;
          if (!reserved[row][c]) {
            const bit = bitIdx < fullBits.length ? fullBits[bitIdx++] : 0;
            // Apply Mask 0: (row + c) % 2 === 0
            const maskedBit = (row + c) % 2 === 0 ? bit ^ 1 : bit;
            grid[row][c] = maskedBit;
          }
        }
      }
      upward = !upward;
    }

    // Format Info for Error Correction Level L (01) + Mask 0 (000) -> 0x77c4
    const formatBits = 0x77c4;
    for (let i = 0; i < 15; i++) {
      const bit = (formatBits >> i) & 1;
      // Top-left format info
      if (i < 6) setModule(i, 8, bit, true);
      else if (i === 6) setModule(7, 8, bit, true);
      else if (i === 7) setModule(8, 8, bit, true);
      else if (i === 8) setModule(8, 7, bit, true);
      else setModule(8, 14 - i, bit, true);

      // Second copy
      if (i < 8) setModule(8, size - 1 - i, bit, true);
      else setModule(size - 15 + i, 8, bit, true);
    }

    return grid;
  }

  return { createMatrix };
})();

// ============================================================================
// REUSABLE QR CODE SVG & CANVAS COMPONENT
// ============================================================================
const QRCodeDisplay = ({ value, size = 140, className = '' }) => {
  const matrix = useMemo(() => QRGenerator.createMatrix(value || 'HACK-EMPTY'), [value]);
  const gridSize = matrix.length;
  const quietZone = 2;
  const totalModules = gridSize + quietZone * 2;

  return (
    <svg
      viewBox={`0 0 ${totalModules} ${totalModules}`}
      width={size}
      height={size}
      shapeRendering="crispEdges"
      className={`bg-white rounded-lg ${className}`}
    >
      <rect width={totalModules} height={totalModules} fill="#ffffff" />
      {matrix.map((row, rIdx) =>
        Array.from(row).map((cell, cIdx) =>
          cell === 1 ? (
            <rect
              key={`${rIdx}-${cIdx}`}
              x={cIdx + quietZone}
              y={rIdx + quietZone}
              width={1}
              height={1}
              fill="#0f172a"
            />
          ) : null
        )
      )}
    </svg>
  );
};

// ============================================================================
// THREE FIXED HACKATHON ATTENDANCE SLOTS (DAY 1 MORNING, DAY 1 NIGHT, DAY 2 MORNING)
// ============================================================================
const ATTENDANCE_SLOTS = [
  {
    id: 'day1_morning',
    shortLabel: 'D1 Morning',
    title: 'Day 1 Morning',
    subtitle: 'Gate Check-In & Inauguration',
    badgeNumber: 'Scan 1 of 3',
    color: 'indigo'
  },
  {
    id: 'day1_night',
    shortLabel: 'D1 Night',
    title: 'Day 1 Night',
    subtitle: 'Midnight Bay Audit & Dinner Check',
    badgeNumber: 'Scan 2 of 3',
    color: 'purple'
  },
  {
    id: 'day2_morning',
    shortLabel: 'D2 Morning',
    title: 'Day 2 Morning',
    subtitle: 'Final Day Roll Call & Pitching Eligibility',
    badgeNumber: 'Scan 3 of 3',
    color: 'emerald'
  }
];

// ============================================================================
// DEFAULT INITIAL STATE (PRE-POPULATED TEAMS, MEMBERS & VOLUNTEERS)
// ============================================================================
const INITIAL_DATA = {
  activeSlotId: 'day1_morning',
  hackathonName: 'NEXUS HACK 2026',
  venueName: 'Main Innovation Arena',
  volunteers: [
    { id: 'vol-1', username: 'volunteer1', password: '123', name: 'Aarav Sharma (Desk A)' },
    { id: 'vol-2', username: 'volunteer2', password: '123', name: 'Priya Nair (Bay Rover)' },
    { id: 'vol-3', username: 'admin_vol', password: '123', name: 'Rohan Verma (Lead)' }
  ],
  teams: [
    {
      id: 'TEAM-101',
      name: 'Neural Ninjas',
      track: 'AI & FinTech',
      bay: 'Bay A-01',
      college: 'IIT Madras',
      members: [
        {
          id: 'HACK26-101-M1',
          name: 'Aditya Krishnan',
          role: 'Team Leader',
          email: 'aditya@iitm.ac.in',
          phone: '9876543210',
          qrCode: 'HACK26-101-M1',
          attendance: {
            day1_morning: { present: true, timestamp: '09:15 AM', scannedBy: 'Aarav Sharma (Desk A)' },
            day1_night: { present: false, timestamp: null, scannedBy: null },
            day2_morning: { present: false, timestamp: null, scannedBy: null }
          }
        },
        {
          id: 'HACK26-101-M2',
          name: 'Meera Sundaram',
          role: 'ML Engineer',
          email: 'meera@iitm.ac.in',
          phone: '9876543211',
          qrCode: 'HACK26-101-M2',
          attendance: {
            day1_morning: { present: false, timestamp: null, scannedBy: null },
            day1_night: { present: false, timestamp: null, scannedBy: null },
            day2_morning: { present: false, timestamp: null, scannedBy: null }
          }
        },
        {
          id: 'HACK26-101-M3',
          name: 'Karthik Raj',
          role: 'Full Stack Dev',
          email: 'karthik@iitm.ac.in',
          phone: '9876543212',
          qrCode: 'HACK26-101-M3',
          attendance: {
            day1_morning: { present: false, timestamp: null, scannedBy: null },
            day1_night: { present: false, timestamp: null, scannedBy: null },
            day2_morning: { present: false, timestamp: null, scannedBy: null }
          }
        }
      ]
    },
    {
      id: 'TEAM-102',
      name: 'Quantum Forge',
      track: 'Cybersecurity & Web3',
      bay: 'Bay A-02',
      college: 'Anna University',
      members: [
        {
          id: 'HACK26-102-M1',
          name: 'Siddharth Menon',
          role: 'Team Leader',
          email: 'siddharth@annauniv.edu',
          phone: '9840112233',
          qrCode: 'HACK26-102-M1',
          attendance: {
            day1_morning: { present: true, timestamp: '09:22 AM', scannedBy: 'Aarav Sharma (Desk A)' },
            day1_night: { present: true, timestamp: '11:40 PM', scannedBy: 'Priya Nair (Bay Rover)' },
            day2_morning: { present: false, timestamp: null, scannedBy: null }
          }
        },
        {
          id: 'HACK26-102-M2',
          name: 'Divya Bharathi',
          role: 'Security Researcher',
          email: 'divya@annauniv.edu',
          phone: '9840112234',
          qrCode: 'HACK26-102-M2',
          attendance: {
            day1_morning: { present: true, timestamp: '09:24 AM', scannedBy: 'Aarav Sharma (Desk A)' },
            day1_night: { present: false, timestamp: null, scannedBy: null },
            day2_morning: { present: false, timestamp: null, scannedBy: null }
          }
        }
      ]
    },
    {
      id: 'TEAM-103',
      name: 'GreenPulse IoT',
      track: 'Climate & Smart Cities',
      bay: 'Bay B-01',
      college: 'SRM Institute',
      members: [
        {
          id: 'HACK26-103-M1',
          name: 'Vikramaditya Rao',
          role: 'Team Leader',
          email: 'vikram@srmist.edu.in',
          phone: '9790123456',
          qrCode: 'HACK26-103-M1',
          attendance: {
            day1_morning: { present: false, timestamp: null, scannedBy: null },
            day1_night: { present: false, timestamp: null, scannedBy: null },
            day2_morning: { present: false, timestamp: null, scannedBy: null }
          }
        },
        {
          id: 'HACK26-103-M2',
          name: 'Ananya Deshmukh',
          role: 'Embedded Systems',
          email: 'ananya@srmist.edu.in',
          phone: '9790123457',
          qrCode: 'HACK26-103-M2',
          attendance: {
            day1_morning: { present: false, timestamp: null, scannedBy: null },
            day1_night: { present: false, timestamp: null, scannedBy: null },
            day2_morning: { present: false, timestamp: null, scannedBy: null }
          }
        }
      ]
    }
  ],
  scanLogs: [
    {
      id: 'log-1',
      timestamp: '09:15 AM',
      memberId: 'HACK26-101-M1',
      memberName: 'Aditya Krishnan',
      teamName: 'Neural Ninjas',
      slotId: 'day1_morning',
      slotTitle: 'Day 1 Morning',
      volunteerName: 'Aarav Sharma (Desk A)'
    },
    {
      id: 'log-2',
      timestamp: '09:22 AM',
      memberId: 'HACK26-102-M1',
      memberName: 'Siddharth Menon',
      teamName: 'Quantum Forge',
      slotId: 'day1_morning',
      slotTitle: 'Day 1 Morning',
      volunteerName: 'Aarav Sharma (Desk A)'
    },
    {
      id: 'log-3',
      timestamp: '11:40 PM',
      memberId: 'HACK26-102-M1',
      memberName: 'Siddharth Menon',
      teamName: 'Quantum Forge',
      slotId: 'day1_night',
      slotTitle: 'Day 1 Night',
      volunteerName: 'Priya Nair (Bay Rover)'
    }
  ]
};

// Helper to count how many of the 3 slots a member has completed
const getMemberScanCount = (member) => {
  if (!member || !member.attendance) return 0;
  return ATTENDANCE_SLOTS.reduce(
    (acc, slot) => acc + (member.attendance[slot.id]?.present ? 1 : 0),
    0
  );
};

// ============================================================================
// MAIN APPLICATION COMPONENT
// ============================================================================
export default function App() {
  // Load state from localStorage or fallback to INITIAL_DATA
  const [store, setStore] = useState(() => {
    try {
      const saved = localStorage.getItem('hackathon_qr_3slot_v1');
      if (saved) return JSON.parse(saved);
    } catch (e) {
      console.warn('Local storage read error:', e);
    }
    return INITIAL_DATA;
  });

  // Portal Navigation: 'landing' | 'admin' | 'volunteer_login' | 'volunteer_portal'
  const [mode, setMode] = useState('landing');
  const [adminTab, setAdminTab] = useState('teams'); // 'teams' | 'idcards' | 'volunteers' | 'reports'

  // Volunteer Auth & Drill-down State
  const [loggedInVolunteer, setLoggedInVolunteer] = useState(null);
  const [volUsername, setVolUsername] = useState('volunteer1');
  const [volPassword, setVolPassword] = useState('123');
  const [volAuthError, setVolAuthError] = useState('');

  // Volunteer Step-by-Step Selection: Team -> Member -> QR Scanner
  const [selectedSlotId, setSelectedSlotId] = useState(store.activeSlotId || 'day1_morning');
  const [selectedTeamId, setSelectedTeamId] = useState(null);
  const [selectedMemberId, setSelectedMemberId] = useState(null);
  const [teamSearchQuery, setTeamSearchQuery] = useState('');

  // Admin Modals & Form States
  const [newTeamName, setNewTeamName] = useState('');
  const [newTeamTrack, setNewTeamTrack] = useState('');
  const [newTeamBay, setNewTeamBay] = useState('');
  const [newTeamCollege, setNewTeamCollege] = useState('');

  const [addingMemberTeamId, setAddingMemberTeamId] = useState(null);
  const [newMemberName, setNewMemberName] = useState('');
  const [newMemberRole, setNewMemberRole] = useState('Member');
  const [newMemberEmail, setNewMemberEmail] = useState('');
  const [newMemberPhone, setNewMemberPhone] = useState('');

  // New Volunteer Form
  const [newVolName, setNewVolName] = useState('');
  const [newVolUser, setNewVolUser] = useState('');
  const [newVolPass, setNewVolPass] = useState('');

  // ID Card Filter
  const [idCardTeamFilter, setIdCardTeamFilter] = useState('ALL');
  const [copiedId, setCopiedId] = useState(null);

  // Camera & QR Scanner State
  const [cameraActive, setCameraActive] = useState(false);
  const [cameraError, setCameraError] = useState('');
  const [manualQrInput, setManualQrInput] = useState('');
  const [scanResultBanner, setScanResultBanner] = useState(null); // { type: 'success' | 'error' | 'warning', title, message }

  const videoRef = useRef(null);
  const canvasRef = useRef(null);
  const scanLoopRef = useRef(null);
  const [user, setUser] = useState(null);
  const [cloudSynced, setCloudSynced] = useState(false);
  const isRemoteUpdateRef = useRef(false);

  // Authenticate and subscribe to Firestore for real-time multi-phone sync
  useEffect(() => {
    if (!auth || !db) return;
    const initAuth = async () => {
      try {
        if (typeof __initial_auth_token !== 'undefined' && __initial_auth_token) {
          await signInWithCustomToken(auth, __initial_auth_token);
        } else {
          await signInAnonymously(auth);
        }
      } catch (err) {
        console.warn('Auth fallback to local mode:', err);
      }
    };
    initAuth();
    const unsubAuth = onAuthStateChanged(auth, (u) => setUser(u));
    return () => unsubAuth();
  }, []);

  useEffect(() => {
    if (!user || !db) return;
    const stateDocRef = doc(db, 'artifacts', appId, 'public', 'data', 'hackathonState', 'main');
    const unsubSnap = onSnapshot(
      stateDocRef,
      (snap) => {
        if (snap.exists()) {
          isRemoteUpdateRef.current = true;
          setStore(snap.data());
          setCloudSynced(true);
        } else {
          setDoc(stateDocRef, store).catch((e) => console.warn('Initial cloud save error:', e));
          setCloudSynced(true);
        }
      },
      (err) => console.warn('Firestore sync error:', err)
    );
    return () => unsubSnap();
  }, [user]);

  // Sync to localStorage & Firebase if available
  useEffect(() => {
    try {
      localStorage.setItem('hackathon_qr_3slot_v1', JSON.stringify(store));
    } catch (e) {
      console.warn('Could not save state to localStorage:', e);
    }
    if (user && db) {
      if (isRemoteUpdateRef.current) {
        isRemoteUpdateRef.current = false;
        return;
      }
      const stateDocRef = doc(db, 'artifacts', appId, 'public', 'data', 'hackathonState', 'main');
      setDoc(stateDocRef, store).catch((e) => console.warn('Cloud sync error:', e));
    }
  }, [store, user]);

  // Export / Import JSON Backup for Offline Multi-Phone Transfer
  const handleExportJsonBackup = () => {
    const dataStr = 'data:text/json;charset=utf-8,' + encodeURIComponent(JSON.stringify(store, null, 2));
    const link = document.createElement('a');
    link.setAttribute('href', dataStr);
    link.setAttribute('download', `hackathon_database_backup.json`);
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
  };

  const handleImportJsonBackup = (e) => {
    const file = e.target.files?.[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = (event) => {
      try {
        const parsed = JSON.parse(event.target.result);
        if (parsed && Array.isArray(parsed.teams)) {
          setStore(parsed);
        }
      } catch (err) {
        console.warn('Invalid JSON backup file:', err);
      }
    };
    reader.readAsText(file);
    e.target.value = '';
  };

  // Keep volunteer selected slot aligned when Admin updates activeSlotId
  useEffect(() => {
    if (store.activeSlotId) {
      setSelectedSlotId(store.activeSlotId);
    }
  }, [store.activeSlotId]);

  // Load jsQR library dynamically for real camera/image QR decoding
  useEffect(() => {
    if (!window.jsQR) {
      const script = document.createElement('script');
      script.src = 'https://cdn.jsdelivr.net/npm/jsqr@1.4.0/dist/jsQR.min.js';
      script.async = true;
      document.body.appendChild(script);
    }
  }, []);

  // Stop camera stream helper
  const stopCamera = () => {
    if (scanLoopRef.current) {
      cancelAnimationFrame(scanLoopRef.current);
      scanLoopRef.current = null;
    }
    if (videoRef.current && videoRef.current.srcObject) {
      const tracks = videoRef.current.srcObject.getTracks();
      tracks.forEach((t) => t.stop());
      videoRef.current.srcObject = null;
    }
    setCameraActive(false);
  };

  useEffect(() => {
    return () => stopCamera();
  }, [selectedMemberId, mode]);

  // Start webcam / mobile back camera for QR scanning
  const startCamera = async () => {
    setCameraError('');
    setScanResultBanner(null);
    try {
      const stream = await navigator.mediaDevices.getUserMedia({
        video: { facingMode: 'environment' }
      });
      if (videoRef.current) {
        videoRef.current.srcObject = stream;
        videoRef.current.setAttribute('playsinline', true);
        await videoRef.current.play();
        setCameraActive(true);
        requestAnimationFrame(tickCameraFrame);
      }
    } catch (err) {
      setCameraError(
        'Camera access unavailable or blocked in this preview. You can upload a QR image or use the Simulator buttons below.'
      );
      setCameraActive(false);
    }
  };

  const tickCameraFrame = () => {
    if (!videoRef.current || !canvasRef.current) return;
    const video = videoRef.current;
    if (video.readyState === video.HAVE_ENOUGH_DATA) {
      const canvas = canvasRef.current;
      const ctx = canvas.getContext('2d');
      canvas.height = video.videoHeight;
      canvas.width = video.videoWidth;
      ctx.drawImage(video, 0, 0, canvas.width, canvas.height);
      if (window.jsQR) {
        const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        const code = window.jsQR(imageData.data, imageData.width, imageData.height, {
          inversionAttempts: 'dontInvert'
        });
        if (code && code.data) {
          handleVerifyQrScan(code.data.trim());
          stopCamera();
          return;
        }
      }
    }
    scanLoopRef.current = requestAnimationFrame(tickCameraFrame);
  };

  // Decode QR code from an uploaded badge/QR image
  const handleQrImageUpload = (e) => {
    const file = e.target.files?.[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = (event) => {
      const img = new Image();
      img.onload = () => {
        const canvas = document.createElement('canvas');
        const ctx = canvas.getContext('2d');
        canvas.width = img.width;
        canvas.height = img.height;
        ctx.drawImage(img, 0, 0);
        if (window.jsQR) {
          const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
          const decoded = window.jsQR(imageData.data, imageData.width, imageData.height);
          if (decoded && decoded.data) {
            handleVerifyQrScan(decoded.data.trim());
          } else {
            setScanResultBanner({
              type: 'error',
              title: 'No QR Code Detected in Image',
              message: 'Could not find a valid QR code in the uploaded image. Try another image or use the Simulator.'
            });
          }
        }
      };
      img.src = event.target.result;
    };
    reader.readAsDataURL(file);
    e.target.value = '';
  };

  // ============================================================================
  // CORE 3-SCAN QR VERIFICATION LOGIC (LOCKED TO CLICKED TEAM & MEMBER)
  // ============================================================================
  const selectedTeam = useMemo(
    () => store.teams.find((t) => t.id === selectedTeamId) || null,
    [store.teams, selectedTeamId]
  );

  const selectedMember = useMemo(
    () => selectedTeam?.members.find((m) => m.id === selectedMemberId) || null,
    [selectedTeam, selectedMemberId]
  );

  const currentSlotObj = useMemo(
    () => ATTENDANCE_SLOTS.find((s) => s.id === selectedSlotId) || ATTENDANCE_SLOTS[0],
    [selectedSlotId]
  );

  const handleVerifyQrScan = (scannedCode) => {
    if (!selectedTeam || !selectedMember) return;

    const cleanScanned = (scannedCode || '').trim();
    if (!cleanScanned) return;

    // 1. Verify that the scanned QR belongs to the exact member clicked by the volunteer
    if (cleanScanned !== selectedMember.qrCode) {
      // Check if it belongs to someone else to show a helpful message
      let otherOwner = null;
      store.teams.forEach((t) => {
        t.members.forEach((m) => {
          if (m.qrCode === cleanScanned) {
            otherOwner = `${m.name} (${t.name})`;
          }
        });
      });

      setScanResultBanner({
        type: 'error',
        title: 'QR Code Mismatch — Wrong Participant!',
        message: otherOwner
          ? `You selected "${selectedMember.name}", but scanned the ID card of ${otherOwner}. Attendance blocked.`
          : `Expected QR "${selectedMember.qrCode}" for ${selectedMember.name}, but scanned "${cleanScanned}".`
      });
      return;
    }

    // 2. Check if all 3/3 slots are already completed
    const currentCount = getMemberScanCount(selectedMember);
    const slotState = selectedMember.attendance?.[selectedSlotId];

    if (slotState?.present) {
      setScanResultBanner({
        type: 'warning',
        title: `Already Scanned for ${currentSlotObj.title}`,
        message: `${selectedMember.name} was already marked PRESENT for ${currentSlotObj.title} at ${slotState.timestamp} by ${slotState.scannedBy}. (${currentCount}/3 Scans Used)`
      });
      return;
    }

    // 3. Valid Match! Record attendance for the active slot (1st, 2nd, or 3rd scan)
    const nowTime = new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    const volunteerLabel = loggedInVolunteer?.name || 'Volunteer';

    setStore((prev) => {
      const updatedTeams = prev.teams.map((t) => {
        if (t.id !== selectedTeam.id) return t;
        return {
          ...t,
          members: t.members.map((m) => {
            if (m.id !== selectedMember.id) return m;
            return {
              ...m,
              attendance: {
                ...m.attendance,
                [selectedSlotId]: {
                  present: true,
                  timestamp: nowTime,
                  scannedBy: volunteerLabel
                }
              }
            };
          })
        };
      });

      const newLog = {
        id: `log-${Date.now()}`,
        timestamp: nowTime,
        memberId: selectedMember.id,
        memberName: selectedMember.name,
        teamName: selectedTeam.name,
        slotId: selectedSlotId,
        slotTitle: currentSlotObj.title,
        volunteerName: volunteerLabel
      };

      return {
        ...prev,
        teams: updatedTeams,
        scanLogs: [newLog, ...prev.scanLogs]
      };
    });

    const newScanCount = currentCount + 1;
    setScanResultBanner({
      type: 'success',
      title: `Attendance Marked — ${currentSlotObj.title} (${newScanCount}/3 Scans)`,
      message: `${selectedMember.name} (${selectedTeam.name}) verified via QR "${selectedMember.qrCode}" at ${nowTime}.`
    });
    setManualQrInput('');
  };

  // ============================================================================
  // ADMIN CRUD HANDLERS (TEAMS, MEMBERS, VOLUNTEERS, SLOTS)
  // ============================================================================
  const handleAddTeam = (e) => {
    e.preventDefault();
    if (!newTeamName.trim()) return;
    const nextNum = 101 + store.teams.length;
    const teamId = `TEAM-${nextNum}`;
    const newTeam = {
      id: teamId,
      name: newTeamName.trim(),
      track: newTeamTrack.trim() || 'General Innovation',
      bay: newTeamBay.trim() || `Bay C-0${store.teams.length + 1}`,
      college: newTeamCollege.trim() || 'Participating Institution',
      members: []
    };
    setStore((prev) => ({
      ...prev,
      teams: [...prev.teams, newTeam]
    }));
    setNewTeamName('');
    setNewTeamTrack('');
    setNewTeamBay('');
    setNewTeamCollege('');
    setAddingMemberTeamId(teamId);
  };

  const handleAddMember = (e, teamId) => {
    e.preventDefault();
    if (!newMemberName.trim()) return;
    const team = store.teams.find((t) => t.id === teamId);
    if (!team) return;

    const teamNumber = teamId.replace('TEAM-', '');
    const memberIndex = team.members.length + 1;
    const uniqueSuffix = Math.floor(100 + Math.random() * 900);
    const uniqueParticipantId = `HACK26-${teamNumber}-M${memberIndex}-${uniqueSuffix}`;

    const newMember = {
      id: uniqueParticipantId,
      name: newMemberName.trim(),
      role: newMemberRole.trim() || 'Member',
      email: newMemberEmail.trim() || 'participant@hackathon.org',
      phone: newMemberPhone.trim() || '—',
      qrCode: uniqueParticipantId,
      attendance: {
        day1_morning: { present: false, timestamp: null, scannedBy: null },
        day1_night: { present: false, timestamp: null, scannedBy: null },
        day2_morning: { present: false, timestamp: null, scannedBy: null }
      }
    };

    setStore((prev) => ({
      ...prev,
      teams: prev.teams.map((t) =>
        t.id === teamId ? { ...t, members: [...t.members, newMember] } : t
      )
    }));

    setNewMemberName('');
    setNewMemberRole('Member');
    setNewMemberEmail('');
    setNewMemberPhone('');
  };

  const handleDeleteMember = (teamId, memberId) => {
    setStore((prev) => ({
      ...prev,
      teams: prev.teams.map((t) =>
        t.id === teamId
          ? { ...t, members: t.members.filter((m) => m.id !== memberId) }
          : t
      )
    }));
  };

  const handleDeleteTeam = (teamId) => {
    setStore((prev) => ({
      ...prev,
      teams: prev.teams.filter((t) => t.id !== teamId)
    }));
  };

  const handleAddVolunteer = (e) => {
    e.preventDefault();
    if (!newVolName.trim() || !newVolUser.trim() || !newVolPass.trim()) return;
    const newVol = {
      id: `vol-${Date.now()}`,
      name: newVolName.trim(),
      username: newVolUser.trim(),
      password: newVolPass.trim()
    };
    setStore((prev) => ({
      ...prev,
      volunteers: [...prev.volunteers, newVol]
    }));
    setNewVolName('');
    setNewVolUser('');
    setNewVolPass('');
  };

  const handleDeleteVolunteer = (volId) => {
    setStore((prev) => ({
      ...prev,
      volunteers: prev.volunteers.filter((v) => v.id !== volId)
    }));
  };

  // Download Individual Printable ID Card as PNG Canvas
  const handleDownloadBadgePng = (member, team) => {
    const canvas = document.createElement('canvas');
    canvas.width = 600;
    canvas.height = 900;
    const ctx = canvas.getContext('2d');

    // Background
    ctx.fillStyle = '#0f172a';
    ctx.fillRect(0, 0, 600, 900);

    // Top Header Gradient Strip
    const grad = ctx.createLinearGradient(0, 0, 600, 180);
    grad.addColorStop(0, '#4f46e5');
    grad.addColorStop(1, '#7c3aed');
    ctx.fillStyle = grad;
    ctx.fillRect(0, 0, 600, 170);

    // Lanyard Slot Cutout
    ctx.fillStyle = '#0f172a';
    ctx.beginPath();
    ctx.roundRect(240, 22, 120, 20, 10);
    ctx.fill();

    // Hackathon Title
    ctx.fillStyle = '#ffffff';
    ctx.font = 'bold 30px sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText(store.hackathonName, 300, 95);

    ctx.fillStyle = '#e0e7ff';
    ctx.font = '18px sans-serif';
    ctx.fillText('OFFICIAL PARTICIPANT PASS (3-SESSION QR)', 300, 132);

    // Participant Name & Role
    ctx.fillStyle = '#ffffff';
    ctx.font = 'bold 34px sans-serif';
    ctx.fillText(member.name, 300, 240);

    ctx.fillStyle = '#38bdf8';
    ctx.font = 'bold 20px sans-serif';
    ctx.fillText(`${member.role.toUpperCase()}  •  ${team.name}`, 300, 280);

    ctx.fillStyle = '#94a3b8';
    ctx.font = '18px sans-serif';
    ctx.fillText(`${team.college}  |  ${team.bay}`, 300, 315);

    // Draw Real QR Code in Center
    const matrix = QRGenerator.createMatrix(member.qrCode);
    const qrSize = 310;
    const quiet = 2;
    const totalModules = matrix.length + quiet * 2;
    const cellSize = qrSize / totalModules;
    const startX = (600 - qrSize) / 2;
    const startY = 355;

    ctx.fillStyle = '#ffffff';
    ctx.beginPath();
    ctx.roundRect(startX - 16, startY - 16, qrSize + 32, qrSize + 32, 20);
    ctx.fill();

    for (let r = 0; r < matrix.length; r++) {
      for (let c = 0; c < matrix.length; c++) {
        if (matrix[r][c] === 1) {
          ctx.fillStyle = '#0f172a';
          ctx.fillRect(
            startX + (c + quiet) * cellSize,
            startY + (r + quiet) * cellSize,
            Math.ceil(cellSize),
            Math.ceil(cellSize)
          );
        }
      }
    }

    // Participant Unique ID
    ctx.fillStyle = '#f8fafc';
    ctx.font = 'bold 22px monospace';
    ctx.fillText(`ID: ${member.qrCode}`, 300, 730);

    // 3-Scan Checkboxes on Bottom of Physical Badge
    ctx.fillStyle = '#94a3b8';
    ctx.font = '16px sans-serif';
    ctx.fillText('VALID FOR 3 OFFICIAL ATTENDANCE SCANS:', 300, 775);

    const slots = ['1. Day 1 Morning', '2. Day 1 Night', '3. Day 2 Morning'];
    slots.forEach((label, idx) => {
      const boxX = 55 + idx * 170;
      ctx.strokeStyle = '#475569';
      ctx.lineWidth = 2;
      ctx.strokeRect(boxX, 800, 150, 48);
      ctx.fillStyle = '#e2e8f0';
      ctx.font = 'bold 14px sans-serif';
      ctx.fillText(label, boxX + 75, 830);
    });

    const link = document.createElement('a');
    link.download = `${member.qrCode}_${member.name.replace(/\s+/g, '_')}_IDCard.png`;
    link.href = canvas.toDataURL('image/png');
    link.click();
  };

  // Export Master 3-Session CSV
  const handleExportCsv = () => {
    const headers = [
      'Team ID',
      'Team Name',
      'Track',
      'Bay',
      'College',
      'Participant ID / QR Code',
      'Member Name',
      'Role',
      'Day 1 Morning Status',
      'Day 1 Morning Time',
      'Day 1 Night Status',
      'Day 1 Night Time',
      'Day 2 Morning Status',
      'Day 2 Morning Time',
      'Total Scans Completed'
    ];

    const rows = [];
    store.teams.forEach((team) => {
      team.members.forEach((m) => {
        const d1m = m.attendance?.day1_morning;
        const d1n = m.attendance?.day1_night;
        const d2m = m.attendance?.day2_morning;
        const count = getMemberScanCount(m);
        rows.push([
          team.id,
          `"${team.name}"`,
          `"${team.track}"`,
          `"${team.bay}"`,
          `"${team.college}"`,
          m.qrCode,
          `"${m.name}"`,
          `"${m.role}"`,
          d1m?.present ? 'PRESENT' : 'ABSENT',
          d1m?.timestamp || '-',
          d1n?.present ? 'PRESENT' : 'ABSENT',
          d1n?.timestamp || '-',
          d2m?.present ? 'PRESENT' : 'ABSENT',
          d2m?.timestamp || '-',
          `${count}/3`
        ]);
      });
    });

    const csvContent =
      'data:text/csv;charset=utf-8,' +
      [headers.join(','), ...rows.map((r) => r.join(','))].join('\n');
    const encodedUri = encodeURI(csvContent);
    const link = document.createElement('a');
    link.setAttribute('href', encodedUri);
    link.setAttribute('download', `Hackathon_3Slot_Attendance_${Date.now()}.csv`);
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
  };

  // Aggregate Stats
  const stats = useMemo(() => {
    let totalMembers = 0;
    let d1MorningPresent = 0;
    let d1NightPresent = 0;
    let d2MorningPresent = 0;
    let allThreeComplete = 0;

    store.teams.forEach((t) => {
      t.members.forEach((m) => {
        totalMembers++;
        if (m.attendance?.day1_morning?.present) d1MorningPresent++;
        if (m.attendance?.day1_night?.present) d1NightPresent++;
        if (m.attendance?.day2_morning?.present) d2MorningPresent++;
        if (getMemberScanCount(m) === 3) allThreeComplete++;
      });
    });

    return {
      totalTeams: store.teams.length,
      totalMembers,
      d1MorningPresent,
      d1NightPresent,
      d2MorningPresent,
      allThreeComplete
    };
  }, [store.teams]);

  // Volunteer Login Handler
  const handleVolunteerLogin = (e) => {
    e.preventDefault();
    const matched = store.volunteers.find(
      (v) =>
        v.username.toLowerCase() === volUsername.trim().toLowerCase() &&
        v.password === volPassword
    );
    if (matched) {
      setLoggedInVolunteer(matched);
      setVolAuthError('');
      setSelectedTeamId(null);
      setSelectedMemberId(null);
      setMode('volunteer_portal');
    } else {
      setVolAuthError('Invalid volunteer username or password. Try volunteer1 / 123');
    }
  };

  // Copy QR ID helper
  const handleCopyQr = (code) => {
    navigator.clipboard?.writeText(code);
    setCopiedId(code);
    setTimeout(() => setCopiedId(null), 1800);
  };

  // ============================================================================
  // VIEW 1: LANDING PORTAL SELECTOR
  // ============================================================================
  if (mode === 'landing') {
    const activeSlot = ATTENDANCE_SLOTS.find((s) => s.id === store.activeSlotId) || ATTENDANCE_SLOTS[0];
    return (
      <div className="min-h-screen bg-slate-950 text-slate-100 flex flex-col justify-between p-4 sm:p-8">
        {/* Top Bar */}
        <header className="max-w-6xl w-full mx-auto flex flex-wrap items-center justify-between gap-4 border-b border-slate-800 pb-5">
          <div className="flex items-center gap-3">
            <div className="w-11 h-11 rounded-xl bg-indigo-600 flex items-center justify-center shadow-lg shadow-indigo-500/30">
              <QrCode className="w-6 h-6 text-white" />
            </div>
            <div>
              <h1 className="text-xl font-bold tracking-tight text-white flex items-center gap-2">
                {store.hackathonName}
                <span className="text-xs px-2.5 py-0.5 rounded-full bg-indigo-500/20 text-indigo-300 border border-indigo-500/30">
                  3-Scan QR System
                </span>
              </h1>
              <p className="text-xs text-slate-400">
                Printable Member ID Cards & Targeted Volunteer Attendance Portal
              </p>
            </div>
          </div>

          <div className="flex flex-wrap items-center gap-2.5">
            <button
              onClick={() => {
                setMode('admin');
                setAdminTab('deploy');
              }}
              className="px-3.5 py-2 rounded-xl bg-indigo-600/20 hover:bg-indigo-600/30 border border-indigo-500/40 text-xs font-semibold text-indigo-300 flex items-center gap-1.5 cursor-pointer"
            >
              <Smartphone className="w-4 h-4" />
              How to Deploy & Use on Phone
            </button>

            <div className="flex items-center gap-3 bg-slate-900 border border-slate-800 px-3.5 py-2 rounded-xl">
              <Clock className="w-4 h-4 text-emerald-400" />
              <div className="text-xs">
                <span className="text-slate-400">Active Session: </span>
                <span className="font-semibold text-emerald-300">{activeSlot.title}</span>
              </div>
            </div>
          </div>
        </header>

        {/* Hero & Role Cards */}
        <main className="max-w-5xl w-full mx-auto my-8 space-y-8">
          <div className="text-center space-y-3 max-w-2xl mx-auto">
            <div className="inline-flex items-center gap-2 px-3 py-1 rounded-full bg-slate-900 border border-slate-800 text-xs text-indigo-300">
              <Sparkles className="w-3.5 h-3.5" />
              1 Unique QR Code Per Member • Scanned 3 Times (D1 Morning • D1 Night • D2 Morning)
            </div>
            <h2 className="text-3xl sm:text-4xl font-extrabold tracking-tight text-white">
              Hackathon ID Card & Attendance Command Center
            </h2>
            <p className="text-slate-400 text-sm sm:text-base">
              Generate printable participant ID cards with unique QR codes, and empower volunteers to mark
              3-round attendance by clicking <span className="text-slate-200 font-medium">Team Name → Member Name → Scan QR</span>.
            </p>
          </div>

          {/* Live 3-Slot Summary Counters */}
          <div className="grid grid-cols-2 sm:grid-cols-4 gap-3 sm:gap-4">
            <div className="bg-slate-900/90 border border-slate-800 rounded-2xl p-4">
              <p className="text-xs text-slate-400">Registered Teams / Members</p>
              <p className="text-2xl font-bold text-white mt-1">
                {stats.totalTeams} Teams <span className="text-sm font-normal text-slate-400">({stats.totalMembers} Members)</span>
              </p>
            </div>
            <div className="bg-slate-900/90 border border-indigo-500/30 rounded-2xl p-4">
              <p className="text-xs text-indigo-300 font-medium">Scan 1: Day 1 Morning</p>
              <p className="text-2xl font-bold text-white mt-1">
                {stats.d1MorningPresent} <span className="text-sm text-slate-400">/ {stats.totalMembers}</span>
              </p>
            </div>
            <div className="bg-slate-900/90 border border-purple-500/30 rounded-2xl p-4">
              <p className="text-xs text-purple-300 font-medium">Scan 2: Day 1 Night</p>
              <p className="text-2xl font-bold text-white mt-1">
                {stats.d1NightPresent} <span className="text-sm text-slate-400">/ {stats.totalMembers}</span>
              </p>
            </div>
            <div className="bg-slate-900/90 border border-emerald-500/30 rounded-2xl p-4">
              <p className="text-xs text-emerald-300 font-medium">Scan 3: Day 2 Morning</p>
              <p className="text-2xl font-bold text-white mt-1">
                {stats.d2MorningPresent} <span className="text-sm text-slate-400">/ {stats.totalMembers}</span>
              </p>
            </div>
          </div>

          {/* Two Main Portal Entry Cards */}
          <div className="grid md:grid-cols-2 gap-6">
            {/* Organizer / Admin Card */}
            <div className="bg-gradient-to-b from-slate-900 to-slate-900/70 border border-slate-800 hover:border-indigo-500/50 rounded-3xl p-6 sm:p-8 flex flex-col justify-between transition-all shadow-xl">
              <div className="space-y-4">
                <div className="w-12 h-12 rounded-2xl bg-indigo-500/20 border border-indigo-500/30 flex items-center justify-center text-indigo-400">
                  <Shield className="w-6 h-6" />
                </div>
                <div>
                  <h3 className="text-2xl font-bold text-white">Organizer Admin Portal</h3>
                  <p className="text-sm text-slate-400 mt-1">
                    Add teams & members, generate unique QR codes, print participant ID cards, and manage volunteer credentials.
                  </p>
                </div>
                <ul className="space-y-2 text-xs sm:text-sm text-slate-300 pt-2">
                  <li className="flex items-center gap-2">
                    <CheckCircle2 className="w-4 h-4 text-indigo-400 shrink-0" />
                    Auto-generate unique QR codes for every team member
                  </li>
                  <li className="flex items-center gap-2">
                    <CheckCircle2 className="w-4 h-4 text-indigo-400 shrink-0" />
                    Printable ID Card Studio (A4 Print & PNG Badge Download)
                  </li>
                  <li className="flex items-center gap-2">
                    <CheckCircle2 className="w-4 h-4 text-indigo-400 shrink-0" />
                    Control active slot (Day 1 Morning, Day 1 Night, Day 2 Morning)
                  </li>
                </ul>
              </div>

              <button
                onClick={() => setMode('admin')}
                className="mt-8 w-full py-3.5 px-5 rounded-xl bg-indigo-600 hover:bg-indigo-500 text-white font-semibold flex items-center justify-center gap-2 shadow-lg shadow-indigo-600/30 transition cursor-pointer"
              >
                Open Organizer Dashboard
                <ChevronRight className="w-4 h-4" />
              </button>
            </div>

            {/* Volunteer Scanner Card */}
            <div className="bg-gradient-to-b from-slate-900 to-slate-900/70 border border-slate-800 hover:border-emerald-500/50 rounded-3xl p-6 sm:p-8 flex flex-col justify-between transition-all shadow-xl">
              <div className="space-y-4">
                <div className="w-12 h-12 rounded-2xl bg-emerald-500/20 border border-emerald-500/30 flex items-center justify-center text-emerald-400">
                  <ScanLine className="w-6 h-6" />
                </div>
                <div>
                  <h3 className="text-2xl font-bold text-white">Volunteer Scan Portal</h3>
                  <p className="text-sm text-slate-400 mt-1">
                    Dedicated login for volunteers to mark participant attendance across all 3 hackathon rounds.
                  </p>
                </div>
                <ul className="space-y-2 text-xs sm:text-sm text-slate-300 pt-2">
                  <li className="flex items-center gap-2">
                    <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0" />
                    Step 1: Click <strong>Team Name</strong> from the list
                  </li>
                  <li className="flex items-center gap-2">
                    <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0" />
                    Step 2: Click <strong>Team Member Name</strong> inside the team
                  </li>
                  <li className="flex items-center gap-2">
                    <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0" />
                    Step 3: Scan Member ID Card QR (Supports 3 Scans per ID Card)
                  </li>
                </ul>
              </div>

              <button
                onClick={() => setMode('volunteer_login')}
                className="mt-8 w-full py-3.5 px-5 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white font-semibold flex items-center justify-center gap-2 shadow-lg shadow-emerald-600/30 transition cursor-pointer"
              >
                Volunteer Login & Scanner
                <LogIn className="w-4 h-4" />
              </button>
            </div>
          </div>
        </main>

        <footer className="max-w-6xl w-full mx-auto text-center text-xs text-slate-500 border-t border-slate-900 pt-4">
          Workflow: Admin Prints Member QR ID Badges → Volunteer Logs In → Selects Team → Selects Member → Scans QR (Day 1 Morning, Day 1 Night, Day 2 Morning)
        </footer>
      </div>
    );
  }

  // ============================================================================
  // VIEW 2: VOLUNTEER LOGIN SCREEN
  // ============================================================================
  if (mode === 'volunteer_login') {
    return (
      <div className="min-h-screen bg-slate-950 text-slate-100 flex items-center justify-center p-4">
        <div className="max-w-md w-full bg-slate-900 border border-slate-800 rounded-3xl p-6 sm:p-8 shadow-2xl space-y-6">
          <button
            onClick={() => setMode('landing')}
            className="inline-flex items-center gap-2 text-xs text-slate-400 hover:text-white cursor-pointer"
          >
            <ArrowLeft className="w-4 h-4" /> Back to Home
          </button>

          <div className="flex items-center gap-3">
            <div className="w-12 h-12 rounded-2xl bg-emerald-500/20 border border-emerald-500/30 flex items-center justify-center text-emerald-400">
              <KeyRound className="w-6 h-6" />
            </div>
            <div>
              <h2 className="text-xl font-bold text-white">Volunteer Portal Login</h2>
              <p className="text-xs text-slate-400">Sign in to verify participant QR ID cards</p>
            </div>
          </div>

          {volAuthError && (
            <div className="p-3 rounded-xl bg-rose-500/10 border border-rose-500/30 text-xs text-rose-300 flex items-center gap-2">
              <AlertTriangle className="w-4 h-4 shrink-0 text-rose-400" />
              {volAuthError}
            </div>
          )}

          <form onSubmit={handleVolunteerLogin} className="space-y-4">
            <div>
              <label className="block text-xs font-medium text-slate-300 mb-1">
                Volunteer Username
              </label>
              <input
                type="text"
                value={volUsername}
                onChange={(e) => setVolUsername(e.target.value)}
                placeholder="e.g. volunteer1"
                className="w-full px-3.5 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-sm text-white focus:outline-none focus:border-emerald-500"
                required
              />
            </div>

            <div>
              <label className="block text-xs font-medium text-slate-300 mb-1">
                Password
              </label>
              <input
                type="password"
                value={volPassword}
                onChange={(e) => setVolPassword(e.target.value)}
                placeholder="Enter password"
                className="w-full px-3.5 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-sm text-white focus:outline-none focus:border-emerald-500"
                required
              />
            </div>

            <button
              type="submit"
              className="w-full py-3 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white font-semibold text-sm flex items-center justify-center gap-2 shadow-lg shadow-emerald-600/25 cursor-pointer"
            >
              <LogIn className="w-4 h-4" />
              Sign In to Volunteer Scanner
            </button>
          </form>

          {/* Quick Demo Credentials Box */}
          <div className="p-3.5 rounded-2xl bg-slate-950 border border-slate-800 space-y-2">
            <p className="text-xs font-semibold text-slate-400">Available Volunteer Accounts (Click to Autofill):</p>
            <div className="flex flex-wrap gap-2">
              {store.volunteers.map((v) => (
                <button
                  key={v.id}
                  type="button"
                  onClick={() => {
                    setVolUsername(v.username);
                    setVolPassword(v.password);
                  }}
                  className="text-xs px-2.5 py-1.5 rounded-lg bg-slate-900 hover:bg-slate-800 border border-slate-700 text-emerald-300 cursor-pointer"
                >
                  {v.username} / {v.password}
                </button>
              ))}
            </div>
          </div>
        </div>
      </div>
    );
  }

  // ============================================================================
  // VIEW 3: VOLUNTEER PORTAL (STEP 1: TEAMS -> STEP 2: MEMBERS -> STEP 3: SCAN QR)
  // ============================================================================
  if (mode === 'volunteer_portal') {
    const filteredTeams = store.teams.filter(
      (t) =>
        t.name.toLowerCase().includes(teamSearchQuery.toLowerCase()) ||
        t.id.toLowerCase().includes(teamSearchQuery.toLowerCase()) ||
        t.bay.toLowerCase().includes(teamSearchQuery.toLowerCase())
    );

    return (
      <div className="min-h-screen bg-slate-950 text-slate-100 flex flex-col">
        {/* Volunteer Header */}
        <header className="bg-slate-900 border-b border-slate-800 px-4 py-3.5 sticky top-0 z-20">
          <div className="max-w-5xl mx-auto flex flex-wrap items-center justify-between gap-3">
            <div className="flex items-center gap-3">
              <div className="w-9 h-9 rounded-xl bg-emerald-600 flex items-center justify-center text-white font-bold">
                <ScanLine className="w-5 h-5" />
              </div>
              <div>
                <div className="flex items-center gap-2">
                  <h1 className="text-sm sm:text-base font-bold text-white">Volunteer Attendance Scanner</h1>
                  <span className="text-[11px] px-2 py-0.5 rounded-full bg-emerald-500/20 text-emerald-300 border border-emerald-500/30">
                    {loggedInVolunteer?.name}
                  </span>
                </div>
                <p className="text-xs text-slate-400">
                  Flow: Select Session → Click Team Name → Click Member Name → Scan QR Code
                </p>
              </div>
            </div>

            <button
              onClick={() => {
                stopCamera();
                setLoggedInVolunteer(null);
                setMode('landing');
              }}
              className="px-3 py-1.5 rounded-xl bg-slate-800 hover:bg-slate-700 text-xs text-slate-200 flex items-center gap-1.5 cursor-pointer"
            >
              <LogOut className="w-3.5 h-3.5" /> Logout
            </button>
          </div>
        </header>

        <main className="max-w-5xl w-full mx-auto p-4 sm:p-6 space-y-6 flex-1">
          {/* 3-Round Attendance Session Selector Bar */}
          <div className="bg-slate-900 border border-slate-800 rounded-2xl p-4 space-y-3">
            <div className="flex flex-wrap items-center justify-between gap-2">
              <span className="text-xs font-semibold uppercase tracking-wider text-slate-400">
                Active Attendance Session (Each QR Can Be Scanned 3 Times):
              </span>
              <span className="text-xs text-emerald-400 font-medium">
                Currently Marking: {currentSlotObj.title} ({currentSlotObj.badgeNumber})
              </span>
            </div>

            <div className="grid grid-cols-1 sm:grid-cols-3 gap-2.5">
              {ATTENDANCE_SLOTS.map((slot) => {
                const isSelected = selectedSlotId === slot.id;
                return (
                  <button
                    key={slot.id}
                    onClick={() => {
                      setSelectedSlotId(slot.id);
                      setScanResultBanner(null);
                    }}
                    className={`p-3 rounded-xl border text-left transition flex items-center justify-between cursor-pointer ${
                      isSelected
                        ? 'bg-emerald-600/20 border-emerald-500 text-white shadow-lg shadow-emerald-950/50'
                        : 'bg-slate-950/70 border-slate-800 text-slate-400 hover:border-slate-700'
                    }`}
                  >
                    <div>
                      <div className="text-xs font-bold flex items-center gap-1.5">
                        {isSelected && <span className="w-2 h-2 rounded-full bg-emerald-400 animate-pulse" />}
                        {slot.title}
                      </div>
                      <p className="text-[11px] opacity-75 mt-0.5">{slot.subtitle}</p>
                    </div>
                    <span className="text-[11px] px-2 py-0.5 rounded-md bg-slate-900 border border-slate-700 font-mono">
                      {slot.badgeNumber}
                    </span>
                  </button>
                );
              })}
            </div>
          </div>

          {/* Interactive Breadcrumb Navigation */}
          <div className="flex flex-wrap items-center gap-2 text-xs sm:text-sm bg-slate-900/60 border border-slate-800/80 px-4 py-2.5 rounded-xl">
            <button
              onClick={() => {
                stopCamera();
                setSelectedTeamId(null);
                setSelectedMemberId(null);
                setScanResultBanner(null);
              }}
              className={`font-semibold cursor-pointer ${
                !selectedTeam ? 'text-emerald-400' : 'text-slate-300 hover:text-white'
              }`}
            >
              1. All Hackathon Teams
            </button>
            <ChevronRight className="w-4 h-4 text-slate-600" />
            <button
              disabled={!selectedTeam}
              onClick={() => {
                stopCamera();
                setSelectedMemberId(null);
                setScanResultBanner(null);
              }}
              className={`font-semibold ${
                selectedTeam && !selectedMember
                  ? 'text-emerald-400'
                  : selectedTeam
                  ? 'text-slate-300 hover:text-white cursor-pointer'
                  : 'text-slate-600 cursor-not-allowed'
              }`}
            >
              2. {selectedTeam ? `Team: ${selectedTeam.name}` : 'Select Team'}
            </button>
            <ChevronRight className="w-4 h-4 text-slate-600" />
            <span
              className={`font-semibold ${
                selectedMember ? 'text-emerald-400' : 'text-slate-600'
              }`}
            >
              3. {selectedMember ? `Scan QR: ${selectedMember.name}` : 'Select Member to Scan'}
            </span>
          </div>

          {/* ================================================================
              STEP 1: LIST OF HACKATHON TEAMS
             ================================================================ */}
          {!selectedTeam && (
            <div className="space-y-4">
              <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-3">
                <div>
                  <h2 className="text-lg font-bold text-white">
                    Step 1: Click a Team Name to View Members
                  </h2>
                  <p className="text-xs text-slate-400">
                    Showing {filteredTeams.length} teams for {currentSlotObj.title}
                  </p>
                </div>

                <div className="relative w-full sm:w-72">
                  <Search className="w-4 h-4 text-slate-400 absolute left-3.5 top-1/2 -translate-y-1/2" />
                  <input
                    type="text"
                    value={teamSearchQuery}
                    onChange={(e) => setTeamSearchQuery(e.target.value)}
                    placeholder="Search team name, ID, or bay..."
                    className="w-full pl-9 pr-4 py-2 rounded-xl bg-slate-900 border border-slate-800 text-xs text-white focus:outline-none focus:border-emerald-500"
                  />
                </div>
              </div>

              <div className="grid sm:grid-cols-2 lg:grid-cols-3 gap-4">
                {filteredTeams.map((team) => {
                  const presentInSlot = team.members.filter(
                    (m) => m.attendance?.[selectedSlotId]?.present
                  ).length;
                  const totalInTeam = team.members.length;
                  const allPresent = totalInTeam > 0 && presentInSlot === totalInTeam;

                  return (
                    <button
                      key={team.id}
                      onClick={() => {
                        setSelectedTeamId(team.id);
                        setSelectedMemberId(null);
                        setScanResultBanner(null);
                      }}
                      className="text-left bg-slate-900 hover:bg-slate-800/90 border border-slate-800 hover:border-emerald-500/50 rounded-2xl p-5 transition-all flex flex-col justify-between group cursor-pointer shadow-md"
                    >
                      <div className="space-y-3">
                        <div className="flex items-center justify-between gap-2">
                          <span className="text-xs font-mono px-2.5 py-0.5 rounded-md bg-slate-950 text-slate-300 border border-slate-800">
                            {team.id}
                          </span>
                          <span className="text-xs text-slate-400 flex items-center gap-1">
                            <MapPin className="w-3.5 h-3.5 text-indigo-400" /> {team.bay}
                          </span>
                        </div>

                        <div>
                          <h3 className="text-lg font-bold text-white group-hover:text-emerald-300 transition flex items-center justify-between">
                            {team.name}
                            <ChevronRight className="w-5 h-5 text-slate-500 group-hover:text-emerald-400 group-hover:translate-x-0.5 transition" />
                          </h3>
                          <p className="text-xs text-slate-400 mt-0.5">
                            {team.track} • {team.college}
                          </p>
                        </div>
                      </div>

                      <div className="mt-5 pt-3 border-t border-slate-800/80 flex items-center justify-between">
                        <span className="text-xs text-slate-400">
                          {currentSlotObj.shortLabel} Attendance:
                        </span>
                        <span
                          className={`text-xs font-bold px-2.5 py-1 rounded-full ${
                            allPresent
                              ? 'bg-emerald-500/20 text-emerald-300 border border-emerald-500/30'
                              : presentInSlot > 0
                              ? 'bg-amber-500/20 text-amber-300 border border-amber-500/30'
                              : 'bg-slate-800 text-slate-400'
                          }`}
                        >
                          {presentInSlot} / {totalInTeam} Present
                        </span>
                      </div>
                    </button>
                  );
                })}
              </div>
            </div>
          )}

          {/* ================================================================
              STEP 2: LIST OF TEAM MEMBERS INSIDE THE CLICKED TEAM
             ================================================================ */}
          {selectedTeam && !selectedMember && (
            <div className="space-y-5">
              <div className="flex flex-wrap items-center justify-between gap-4 bg-slate-900 border border-slate-800 rounded-2xl p-5">
                <div>
                  <button
                    onClick={() => setSelectedTeamId(null)}
                    className="inline-flex items-center gap-1.5 text-xs text-emerald-400 hover:underline mb-1 cursor-pointer"
                  >
                    <ArrowLeft className="w-3.5 h-3.5" /> Back to All Teams
                  </button>
                  <h2 className="text-xl font-bold text-white">
                    Step 2: Select a Member from "{selectedTeam.name}"
                  </h2>
                  <p className="text-xs text-slate-400">
                    Click on a team member's name below to open their QR code scanner for{' '}
                    <strong className="text-slate-200">{currentSlotObj.title}</strong>.
                  </p>
                </div>

                <div className="text-right">
                  <span className="text-xs px-3 py-1.5 rounded-xl bg-slate-950 border border-slate-800 text-slate-300 font-mono">
                    {selectedTeam.id} • {selectedTeam.bay}
                  </span>
                </div>
              </div>

              <div className="grid sm:grid-cols-2 gap-4">
                {selectedTeam.members.map((member) => {
                  const isPresentCurrent = member.attendance?.[selectedSlotId]?.present;
                  const scanCount = getMemberScanCount(member);

                  return (
                    <button
                      key={member.id}
                      onClick={() => {
                        setSelectedMemberId(member.id);
                        setScanResultBanner(null);
                      }}
                      className={`text-left rounded-2xl p-5 border transition-all flex flex-col justify-between cursor-pointer ${
                        isPresentCurrent
                          ? 'bg-emerald-950/20 border-emerald-500/40 hover:border-emerald-400'
                          : 'bg-slate-900 border-slate-800 hover:border-indigo-500'
                      }`}
                    >
                      <div className="flex items-start justify-between gap-3">
                        <div>
                          <span className="text-[11px] font-mono text-indigo-300 bg-indigo-500/10 px-2 py-0.5 rounded border border-indigo-500/20">
                            {member.qrCode}
                          </span>
                          <h3 className="text-lg font-bold text-white mt-2 flex items-center gap-2">
                            {member.name}
                          </h3>
                          <p className="text-xs text-slate-400">{member.role}</p>
                        </div>

                        <div className="text-right">
                          <span
                            className={`inline-flex items-center gap-1 text-xs font-bold px-2.5 py-1 rounded-full ${
                              isPresentCurrent
                                ? 'bg-emerald-500/20 text-emerald-300 border border-emerald-500/30'
                                : 'bg-amber-500/15 text-amber-300 border border-amber-500/30'
                            }`}
                          >
                            {isPresentCurrent ? (
                              <>
                                <CheckCircle2 className="w-3.5 h-3.5" /> Present
                              </>
                            ) : (
                              <>
                                <QrCode className="w-3.5 h-3.5" /> Tap to Scan QR
                              </>
                            )}
                          </span>
                          <p className="text-[11px] text-slate-400 mt-1.5 font-mono">
                            Total Scans: {scanCount}/3
                          </p>
                        </div>
                      </div>

                      {/* 3-Round Status Pills on Member Card */}
                      <div className="mt-4 pt-3 border-t border-slate-800/80 grid grid-cols-3 gap-2">
                        {ATTENDANCE_SLOTS.map((slot) => {
                          const slotDone = member.attendance?.[slot.id]?.present;
                          return (
                            <div
                              key={slot.id}
                              className={`px-2 py-1.5 rounded-lg text-[11px] border text-center ${
                                slotDone
                                  ? 'bg-emerald-500/15 border-emerald-500/30 text-emerald-300 font-semibold'
                                  : 'bg-slate-950 border-slate-800 text-slate-500'
                              }`}
                            >
                              <div>{slot.shortLabel}</div>
                              <div className="text-[10px] opacity-80">
                                {slotDone ? member.attendance[slot.id].timestamp : 'Pending'}
                              </div>
                            </div>
                          );
                        })}
                      </div>
                    </button>
                  );
                })}
              </div>
            </div>
          )}

          {/* ================================================================
              STEP 3: TARGETED MEMBER QR SCANNER (3-SCAN VERIFICATION)
             ================================================================ */}
          {selectedTeam && selectedMember && (
            <div className="space-y-6">
              <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 flex flex-wrap items-center justify-between gap-4">
                <div>
                  <button
                    onClick={() => {
                      stopCamera();
                      setSelectedMemberId(null);
                      setScanResultBanner(null);
                    }}
                    className="inline-flex items-center gap-1.5 text-xs text-emerald-400 hover:underline mb-1 cursor-pointer"
                  >
                    <ArrowLeft className="w-3.5 h-3.5" /> Back to {selectedTeam.name} Members
                  </button>
                  <h2 className="text-xl font-bold text-white">
                    Step 3: Scan ID Card QR for {selectedMember.name}
                  </h2>
                  <p className="text-xs text-slate-400">
                    Team: <strong className="text-slate-200">{selectedTeam.name}</strong> • Expected QR ID:{' '}
                    <span className="font-mono text-indigo-300">{selectedMember.qrCode}</span>
                  </p>
                </div>

                <div className="flex items-center gap-3">
                  <div className="text-right">
                    <div className="text-xs text-slate-400">3-Session Progress</div>
                    <div className="text-lg font-extrabold text-emerald-400">
                      {getMemberScanCount(selectedMember)} / 3 Scans Completed
                    </div>
                  </div>
                </div>
              </div>

              {/* Scan Result Alert Banner */}
              {scanResultBanner && (
                <div
                  className={`p-4 rounded-2xl border flex items-start gap-3 ${
                    scanResultBanner.type === 'success'
                      ? 'bg-emerald-500/15 border-emerald-500/40 text-emerald-200'
                      : scanResultBanner.type === 'warning'
                      ? 'bg-amber-500/15 border-amber-500/40 text-amber-200'
                      : 'bg-rose-500/15 border-rose-500/40 text-rose-200'
                  }`}
                >
                  {scanResultBanner.type === 'success' ? (
                    <CheckCircle2 className="w-6 h-6 text-emerald-400 shrink-0 mt-0.5" />
                  ) : scanResultBanner.type === 'warning' ? (
                    <AlertTriangle className="w-6 h-6 text-amber-400 shrink-0 mt-0.5" />
                  ) : (
                    <XCircle className="w-6 h-6 text-rose-400 shrink-0 mt-0.5" />
                  )}
                  <div className="flex-1">
                    <h4 className="font-bold text-sm">{scanResultBanner.title}</h4>
                    <p className="text-xs mt-1 opacity-90">{scanResultBanner.message}</p>
                  </div>
                </div>
              )}

              <div className="grid md:grid-cols-2 gap-6">
                {/* Left Column: Live Camera Scanner + Upload + Simulator */}
                <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 space-y-4">
                  <div className="flex items-center justify-between">
                    <h3 className="text-sm font-bold text-white flex items-center gap-2">
                      <Camera className="w-4 h-4 text-emerald-400" />
                      Scan Printed ID Card QR ({currentSlotObj.title})
                    </h3>
                    {cameraActive ? (
                      <button
                        onClick={stopCamera}
                        className="text-xs px-3 py-1 rounded-lg bg-rose-600/20 text-rose-300 border border-rose-500/30 cursor-pointer"
                      >
                        Stop Camera
                      </button>
                    ) : (
                      <button
                        onClick={startCamera}
                        className="text-xs px-3 py-1.5 rounded-lg bg-emerald-600 hover:bg-emerald-500 text-white font-semibold cursor-pointer"
                      >
                        Open Camera Scanner
                      </button>
                    )}
                  </div>

                  {/* Camera Viewport */}
                  <div className="relative aspect-video bg-slate-950 rounded-xl border border-slate-800 overflow-hidden flex items-center justify-center">
                    <video
                      ref={videoRef}
                      className={`w-full h-full object-cover ${cameraActive ? 'block' : 'hidden'}`}
                    />
                    <canvas ref={canvasRef} className="hidden" />
                    {!cameraActive && (
                      <div className="text-center p-6 space-y-2">
                        <QrCode className="w-10 h-10 text-slate-600 mx-auto" />
                        <p className="text-xs text-slate-400">
                          Click <strong>"Open Camera Scanner"</strong> to scan {selectedMember.name}'s ID card, or use the quick options below.
                        </p>
                      </div>
                    )}
                  </div>

                  {cameraError && (
                    <p className="text-xs text-amber-300 bg-amber-500/10 border border-amber-500/20 p-2.5 rounded-xl">
                      {cameraError}
                    </p>
                  )}

                  {/* Option B: Upload QR Badge Image */}
                  <div className="pt-2 border-t border-slate-800 flex flex-wrap items-center justify-between gap-2">
                    <span className="text-xs text-slate-400">Or scan from downloaded ID Card PNG:</span>
                    <label className="text-xs px-3 py-1.5 rounded-xl bg-slate-800 hover:bg-slate-700 text-slate-200 cursor-pointer inline-flex items-center gap-1.5">
                      <Upload className="w-3.5 h-3.5" />
                      Upload QR Image
                      <input
                        type="file"
                        accept="image/*"
                        onChange={handleQrImageUpload}
                        className="hidden"
                      />
                    </label>
                  </div>

                  {/* Option C: One-Click QR Hardware Scan Simulator for Instant Testing */}
                  <div className="p-4 rounded-xl bg-slate-950 border border-slate-800 space-y-3">
                    <p className="text-xs font-semibold text-indigo-300 flex items-center gap-1.5">
                      <Sparkles className="w-3.5 h-3.5" />
                      Instant QR Scan Simulator (Test 3-Scan Lifecycle & Mismatch Protection):
                    </p>
                    <div className="grid grid-cols-1 sm:grid-cols-2 gap-2">
                      <button
                        type="button"
                        onClick={() => handleVerifyQrScan(selectedMember.qrCode)}
                        className="py-2.5 px-3 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white font-semibold text-xs flex items-center justify-center gap-1.5 shadow cursor-pointer"
                      >
                        <QrCode className="w-4 h-4" />
                        Simulate Scanning {selectedMember.name}'s QR
                      </button>

                      <button
                        type="button"
                        onClick={() => handleVerifyQrScan('HACK26-WRONG-ID-999')}
                        className="py-2.5 px-3 rounded-xl bg-slate-800 hover:bg-slate-700 text-rose-300 border border-rose-500/30 font-semibold text-xs flex items-center justify-center gap-1.5 cursor-pointer"
                      >
                        <XCircle className="w-4 h-4" />
                        Simulate Wrong Person's QR
                      </button>
                    </div>

                    {/* Manual QR String Input */}
                    <form
                      onSubmit={(e) => {
                        e.preventDefault();
                        handleVerifyQrScan(manualQrInput);
                      }}
                      className="flex gap-2 pt-1"
                    >
                      <input
                        type="text"
                        value={manualQrInput}
                        onChange={(e) => setManualQrInput(e.target.value)}
                        placeholder={`Enter QR payload (${selectedMember.qrCode})`}
                        className="flex-1 px-3 py-1.5 rounded-lg bg-slate-900 border border-slate-800 text-xs text-white font-mono"
                      />
                      <button
                        type="submit"
                        className="px-3 py-1.5 rounded-lg bg-indigo-600 hover:bg-indigo-500 text-white text-xs font-semibold cursor-pointer"
                      >
                        Verify
                      </button>
                    </form>
                  </div>
                </div>

                {/* Right Column: Member's 3-Scan Status Card & ID Preview */}
                <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 flex flex-col justify-between space-y-5">
                  <div className="space-y-4">
                    <div className="flex items-center justify-between border-b border-slate-800 pb-3">
                      <div>
                        <h3 className="text-base font-bold text-white">{selectedMember.name}</h3>
                        <p className="text-xs text-slate-400">
                          {selectedMember.role} • {selectedTeam.name}
                        </p>
                      </div>
                      <QRCodeDisplay value={selectedMember.qrCode} size={64} />
                    </div>

                    <div className="space-y-2.5">
                      <p className="text-xs font-semibold uppercase tracking-wider text-slate-400">
                        3-Session QR Attendance Log for this ID Card:
                      </p>

                      {ATTENDANCE_SLOTS.map((slot, index) => {
                        const record = selectedMember.attendance?.[slot.id];
                        const isCurrentSlot = selectedSlotId === slot.id;

                        return (
                          <div
                            key={slot.id}
                            onClick={() => setSelectedSlotId(slot.id)}
                            className={`p-3.5 rounded-xl border transition flex items-center justify-between cursor-pointer ${
                              record?.present
                                ? 'bg-emerald-950/30 border-emerald-500/40'
                                : isCurrentSlot
                                ? 'bg-indigo-950/30 border-indigo-500/50'
                                : 'bg-slate-950 border-slate-800'
                            }`}
                          >
                            <div className="space-y-0.5">
                              <div className="flex items-center gap-2">
                                <span className="text-xs font-bold text-white">
                                  Scan {index + 1}: {slot.title}
                                </span>
                                {isCurrentSlot && (
                                  <span className="text-[10px] px-2 py-0.5 rounded bg-indigo-500/20 text-indigo-300 border border-indigo-500/30">
                                    Selected Slot
                                  </span>
                                )}
                              </div>
                              <p className="text-[11px] text-slate-400">
                                {record?.present
                                  ? `Scanned at ${record.timestamp} by ${record.scannedBy}`
                                  : 'Not scanned yet — Click slot & scan QR'}
                              </p>
                            </div>

                            <div>
                              {record?.present ? (
                                <span className="inline-flex items-center gap-1 text-xs font-bold text-emerald-400 bg-emerald-500/15 px-2.5 py-1 rounded-full border border-emerald-500/30">
                                  <CheckCircle2 className="w-3.5 h-3.5" /> Present
                                </span>
                              ) : (
                                <span className="text-xs text-slate-500 font-medium px-2.5 py-1 rounded-full bg-slate-900 border border-slate-800">
                                  Pending
                                </span>
                              )}
                            </div>
                          </div>
                        );
                      })}
                    </div>
                  </div>

                  <div className="p-3.5 rounded-xl bg-slate-950 border border-slate-800 flex items-center justify-between">
                    <div className="text-xs text-slate-400">
                      Switch session above to test scanning the <strong>exact same QR code</strong> across Day 1 Morning, Day 1 Night, and Day 2 Morning.
                    </div>
                  </div>
                </div>
              </div>
            </div>
          )}
        </main>
      </div>
    );
  }

  // ============================================================================
  // VIEW 4: ORGANIZER ADMIN PORTAL (TEAMS, PRINTABLE ID CARDS, VOLUNTEERS, LOGS)
  // ============================================================================
  const idCardTeams =
    idCardTeamFilter === 'ALL'
      ? store.teams
      : store.teams.filter((t) => t.id === idCardTeamFilter);

  return (
    <div className="min-h-screen bg-slate-950 text-slate-100 flex flex-col">
      {/* Top Admin Navbar (Hidden when printing ID Cards) */}
      <header className="bg-slate-900 border-b border-slate-800 px-4 sm:px-6 py-3.5 print:hidden">
        <div className="max-w-7xl mx-auto flex flex-wrap items-center justify-between gap-4">
          <div className="flex items-center gap-3">
            <button
              onClick={() => setMode('landing')}
              className="p-2 rounded-xl bg-slate-800 hover:bg-slate-700 text-slate-300 cursor-pointer"
              title="Back to Role Selector"
            >
              <ArrowLeft className="w-4 h-4" />
            </button>
            <div>
              <h1 className="text-base sm:text-lg font-bold text-white flex items-center gap-2">
                Organizer Admin Portal
                <span className="text-xs px-2.5 py-0.5 rounded-full bg-indigo-500/20 text-indigo-300 border border-indigo-500/30">
                  {store.hackathonName}
                </span>
              </h1>
              <p className="text-xs text-slate-400">
                Manage Teams, Print Member QR ID Cards, and Track 3-Session Attendance
              </p>
            </div>
          </div>

          {/* Active Session Switcher for Event Control */}
          <div className="flex flex-wrap items-center gap-2">
            <span className="text-xs text-slate-400">Default Active Session:</span>
            <select
              value={store.activeSlotId}
              onChange={(e) =>
                setStore((prev) => ({ ...prev, activeSlotId: e.target.value }))
              }
              className="px-3 py-1.5 rounded-xl bg-slate-950 border border-indigo-500/40 text-xs text-indigo-200 font-semibold focus:outline-none"
            >
              {ATTENDANCE_SLOTS.map((s) => (
                <option key={s.id} value={s.id}>
                  {s.title} ({s.badgeNumber})
                </option>
              ))}
            </select>

            <button
              onClick={() => setMode('volunteer_login')}
              className="px-3 py-1.5 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white text-xs font-semibold flex items-center gap-1.5 cursor-pointer"
            >
              <ScanLine className="w-3.5 h-3.5" /> Switch to Volunteer View
            </button>
          </div>
        </div>

        {/* Admin Navigation Tabs */}
        <div className="max-w-7xl mx-auto flex flex-wrap gap-2 mt-4 pt-3 border-t border-slate-800/80">
          {[
            { id: 'teams', label: '1. Teams & Member Roster', icon: Users },
            { id: 'idcards', label: '2. Printable ID Cards (QR Badges)', icon: Printer },
            { id: 'volunteers', label: '3. Volunteer Login Credentials', icon: KeyRound },
            { id: 'reports', label: '4. 3-Session Attendance & CSV Export', icon: FileSpreadsheet },
            { id: 'deploy', label: '5. Deploy & Use on Phone', icon: Smartphone }
          ].map((tab) => {
            const Icon = tab.icon;
            const active = adminTab === tab.id;
            return (
              <button
                key={tab.id}
                onClick={() => setAdminTab(tab.id)}
                className={`px-4 py-2 rounded-xl text-xs sm:text-sm font-semibold flex items-center gap-2 transition cursor-pointer ${
                  active
                    ? 'bg-indigo-600 text-white shadow-lg shadow-indigo-600/25'
                    : 'bg-slate-950/60 text-slate-400 hover:text-white hover:bg-slate-800'
                }`}
              >
                <Icon className="w-4 h-4" />
                {tab.label}
              </button>
            );
          })}
        </div>
      </header>

      {/* Main Content Area */}
      <main className="max-w-7xl w-full mx-auto p-4 sm:p-6 flex-1 space-y-6">
        {/* ====================================================================
            TAB 1: TEAMS & MEMBER ROSTER (AUTO-GENERATES UNIQUE QR PER MEMBER)
           ==================================================================== */}
        {adminTab === 'teams' && (
          <div className="grid lg:grid-cols-3 gap-6">
            {/* Left Column: Create New Team Form */}
            <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 h-fit space-y-4">
              <div className="flex items-center gap-2.5">
                <div className="w-9 h-9 rounded-xl bg-indigo-500/20 border border-indigo-500/30 flex items-center justify-center text-indigo-400">
                  <Plus className="w-5 h-5" />
                </div>
                <div>
                  <h2 className="text-base font-bold text-white">Add Hackathon Team</h2>
                  <p className="text-xs text-slate-400">Create a team, then add members to generate QR codes</p>
                </div>
              </div>

              <form onSubmit={handleAddTeam} className="space-y-3">
                <div>
                  <label className="block text-xs text-slate-300 mb-1">Team Name *</label>
                  <input
                    type="text"
                    value={newTeamName}
                    onChange={(e) => setNewTeamName(e.target.value)}
                    placeholder="e.g. Cyber Titans"
                    className="w-full px-3 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                    required
                  />
                </div>
                <div>
                  <label className="block text-xs text-slate-300 mb-1">Track / Domain</label>
                  <input
                    type="text"
                    value={newTeamTrack}
                    onChange={(e) => setNewTeamTrack(e.target.value)}
                    placeholder="e.g. GenAI & Healthcare"
                    className="w-full px-3 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                  />
                </div>
                <div className="grid grid-cols-2 gap-2">
                  <div>
                    <label className="block text-xs text-slate-300 mb-1">Bay / Table No.</label>
                    <input
                      type="text"
                      value={newTeamBay}
                      onChange={(e) => setNewTeamBay(e.target.value)}
                      placeholder="e.g. Bay C-04"
                      className="w-full px-3 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                    />
                  </div>
                  <div>
                    <label className="block text-xs text-slate-300 mb-1">College / Org</label>
                    <input
                      type="text"
                      value={newTeamCollege}
                      onChange={(e) => setNewTeamCollege(e.target.value)}
                      placeholder="e.g. NIT Trichy"
                      className="w-full px-3 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                    />
                  </div>
                </div>
                <button
                  type="submit"
                  className="w-full py-2.5 rounded-xl bg-indigo-600 hover:bg-indigo-500 text-white font-semibold text-xs flex items-center justify-center gap-1.5 cursor-pointer"
                >
                  <Plus className="w-4 h-4" /> Create Team
                </button>
              </form>
            </div>

            {/* Right 2 Columns: List of Teams & Their Members */}
            <div className="lg:col-span-2 space-y-4">
              {store.teams.map((team) => (
                <div
                  key={team.id}
                  className="bg-slate-900 border border-slate-800 rounded-2xl p-5 space-y-4"
                >
                  <div className="flex flex-wrap items-center justify-between gap-2 border-b border-slate-800 pb-3">
                    <div>
                      <div className="flex items-center gap-2">
                        <span className="text-xs font-mono px-2 py-0.5 rounded bg-indigo-500/20 text-indigo-300 border border-indigo-500/30">
                          {team.id}
                        </span>
                        <h3 className="text-lg font-bold text-white">{team.name}</h3>
                      </div>
                      <p className="text-xs text-slate-400 mt-0.5">
                        {team.track} • {team.bay} • {team.college}
                      </p>
                    </div>

                    <div className="flex items-center gap-2">
                      <button
                        onClick={() =>
                          setAddingMemberTeamId(
                            addingMemberTeamId === team.id ? null : team.id
                          )
                        }
                        className="px-3 py-1.5 rounded-xl bg-indigo-600/20 hover:bg-indigo-600/30 text-indigo-300 border border-indigo-500/30 text-xs font-semibold flex items-center gap-1.5 cursor-pointer"
                      >
                        <UserPlus className="w-3.5 h-3.5" /> Add Team Member
                      </button>
                      <button
                        onClick={() => handleDeleteTeam(team.id)}
                        className="p-1.5 rounded-lg bg-slate-800 hover:bg-rose-950 text-slate-400 hover:text-rose-400 cursor-pointer"
                        title="Delete Team"
                      >
                        <Trash2 className="w-4 h-4" />
                      </button>
                    </div>
                  </div>

                  {/* Quick Add Member Form for this Team */}
                  {addingMemberTeamId === team.id && (
                    <form
                      onSubmit={(e) => handleAddMember(e, team.id)}
                      className="p-4 rounded-xl bg-slate-950 border border-indigo-500/40 space-y-3"
                    >
                      <p className="text-xs font-bold text-indigo-300">
                        Add New Member to {team.name} (Unique QR Code Auto-Generated)
                      </p>
                      <div className="grid sm:grid-cols-2 gap-2.5">
                        <input
                          type="text"
                          value={newMemberName}
                          onChange={(e) => setNewMemberName(e.target.value)}
                          placeholder="Participant Full Name *"
                          className="px-3 py-2 rounded-lg bg-slate-900 border border-slate-800 text-xs text-white"
                          required
                        />
                        <input
                          type="text"
                          value={newMemberRole}
                          onChange={(e) => setNewMemberRole(e.target.value)}
                          placeholder="Role (e.g. Team Leader / UI Dev)"
                          className="px-3 py-2 rounded-lg bg-slate-900 border border-slate-800 text-xs text-white"
                        />
                        <input
                          type="email"
                          value={newMemberEmail}
                          onChange={(e) => setNewMemberEmail(e.target.value)}
                          placeholder="Email Address"
                          className="px-3 py-2 rounded-lg bg-slate-900 border border-slate-800 text-xs text-white"
                        />
                        <input
                          type="text"
                          value={newMemberPhone}
                          onChange={(e) => setNewMemberPhone(e.target.value)}
                          placeholder="Phone Number"
                          className="px-3 py-2 rounded-lg bg-slate-900 border border-slate-800 text-xs text-white"
                        />
                      </div>
                      <div className="flex justify-end gap-2">
                        <button
                          type="button"
                          onClick={() => setAddingMemberTeamId(null)}
                          className="px-3 py-1.5 rounded-lg bg-slate-800 text-xs text-slate-300 cursor-pointer"
                        >
                          Cancel
                        </button>
                        <button
                          type="submit"
                          className="px-4 py-1.5 rounded-lg bg-indigo-600 hover:bg-indigo-500 text-xs font-semibold text-white cursor-pointer"
                        >
                          Generate Member QR & Save
                        </button>
                      </div>
                    </form>
                  )}

                  {/* Team Members Table/Cards */}
                  <div className="space-y-2.5">
                    {team.members.map((member) => (
                      <div
                        key={member.id}
                        className="p-3 rounded-xl bg-slate-950/90 border border-slate-800/90 flex flex-wrap items-center justify-between gap-3"
                      >
                        <div className="flex items-center gap-3">
                          <QRCodeDisplay value={member.qrCode} size={52} />
                          <div>
                            <div className="flex items-center gap-2">
                              <h4 className="text-sm font-bold text-white">{member.name}</h4>
                              <span className="text-[11px] px-2 py-0.5 rounded bg-slate-900 text-slate-300 border border-slate-800">
                                {member.role}
                              </span>
                            </div>
                            <div className="flex items-center gap-2 mt-1">
                              <span className="text-xs font-mono text-indigo-400">
                                QR: {member.qrCode}
                              </span>
                              <button
                                onClick={() => handleCopyQr(member.qrCode)}
                                className="text-[11px] text-slate-400 hover:text-white inline-flex items-center gap-1 cursor-pointer"
                              >
                                {copiedId === member.qrCode ? (
                                  <Check className="w-3 h-3 text-emerald-400" />
                                ) : (
                                  <Copy className="w-3 h-3" />
                                )}
                              </button>
                            </div>
                          </div>
                        </div>

                        {/* 3-Session Status Indicators + Actions */}
                        <div className="flex flex-wrap items-center gap-2">
                          {ATTENDANCE_SLOTS.map((slot) => {
                            const isPresent = member.attendance?.[slot.id]?.present;
                            return (
                              <span
                                key={slot.id}
                                className={`text-[11px] px-2.5 py-1 rounded-lg border font-medium ${
                                  isPresent
                                    ? 'bg-emerald-500/15 border-emerald-500/30 text-emerald-300'
                                    : 'bg-slate-900 border-slate-800 text-slate-500'
                                }`}
                              >
                                {slot.shortLabel}: {isPresent ? '✓' : '—'}
                              </span>
                            );
                          })}

                          <button
                            onClick={() => handleDownloadBadgePng(member, team)}
                            className="p-2 rounded-lg bg-slate-900 hover:bg-slate-800 text-indigo-300 border border-slate-800 cursor-pointer"
                            title="Download Printable ID Card PNG"
                          >
                            <Download className="w-4 h-4" />
                          </button>

                          <button
                            onClick={() => handleDeleteMember(team.id, member.id)}
                            className="p-2 rounded-lg bg-slate-900 hover:bg-rose-950 text-slate-500 hover:text-rose-400 border border-slate-800 cursor-pointer"
                            title="Remove Member"
                          >
                            <Trash2 className="w-4 h-4" />
                          </button>
                        </div>
                      </div>
                    ))}
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* ====================================================================
            TAB 2: PRINTABLE ID CARD STUDIO (QR BADGES FOR LANYARDS)
           ==================================================================== */}
        {adminTab === 'idcards' && (
          <div className="space-y-6">
            {/* Control Bar (Hidden when printing) */}
            <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 flex flex-wrap items-center justify-between gap-4 print:hidden">
              <div>
                <h2 className="text-lg font-bold text-white">
                  Printable Participant ID Cards (With Unique 3-Session QR Codes)
                </h2>
                <p className="text-xs text-slate-400">
                  Print directly onto A4 badge sheets or download individual PNG ID cards for each team member.
                </p>
              </div>

              <div className="flex flex-wrap items-center gap-3">
                <select
                  value={idCardTeamFilter}
                  onChange={(e) => setIdCardTeamFilter(e.target.value)}
                  className="px-3.5 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                >
                  <option value="ALL">All Teams ({stats.totalMembers} Badges)</option>
                  {store.teams.map((t) => (
                    <option key={t.id} value={t.id}>
                      {t.name} ({t.members.length} Members)
                    </option>
                  ))}
                </select>

                <button
                  onClick={() => window.print()}
                  className="px-4 py-2 rounded-xl bg-indigo-600 hover:bg-indigo-500 text-white text-xs font-semibold flex items-center gap-2 shadow-lg shadow-indigo-600/25 cursor-pointer"
                >
                  <Printer className="w-4 h-4" /> Print All ID Cards
                </button>
              </div>
            </div>

            {/* Printable Badge Grid */}
            <div className="grid sm:grid-cols-2 lg:grid-cols-3 gap-6 print:grid-cols-2 print:gap-4">
              {idCardTeams.flatMap((team) =>
                team.members.map((member) => (
                  <div
                    key={member.id}
                    className="bg-slate-900 border-2 border-slate-800 rounded-3xl overflow-hidden shadow-xl flex flex-col justify-between print:border-slate-400 print:break-inside-avoid"
                  >
                    {/* Badge Header with Lanyard Slot */}
                    <div className="bg-gradient-to-r from-indigo-600 to-purple-600 p-4 text-center relative">
                      <div className="w-16 h-2.5 bg-slate-950/80 rounded-full mx-auto mb-3" />
                      <h3 className="text-sm font-extrabold tracking-wider text-white uppercase">
                        {store.hackathonName}
                      </h3>
                      <p className="text-[10px] text-indigo-100 tracking-widest uppercase mt-0.5">
                        Official Participant ID Card
                      </p>
                    </div>

                    {/* Badge Body & QR Code */}
                    <div className="p-6 text-center space-y-4 flex-1 flex flex-col items-center justify-center">
                      <div>
                        <h4 className="text-xl font-extrabold text-white">{member.name}</h4>
                        <p className="text-xs font-semibold text-indigo-400 mt-0.5">
                          {member.role} • {team.name}
                        </p>
                        <p className="text-[11px] text-slate-400 mt-0.5">
                          {team.college} ({team.bay})
                        </p>
                      </div>

                      <div className="p-3 bg-white rounded-2xl shadow-inner inline-block">
                        <QRCodeDisplay value={member.qrCode} size={156} />
                      </div>

                      <div className="space-y-1">
                        <p className="text-xs font-mono font-bold text-slate-200 bg-slate-950 px-3 py-1 rounded-lg border border-slate-800">
                          {member.qrCode}
                        </p>
                        <p className="text-[10px] text-slate-400">
                          Valid for 3 Scans: Day 1 Morning • Day 1 Night • Day 2 Morning
                        </p>
                      </div>
                    </div>

                    {/* Badge Footer */}
                    <div className="px-5 py-3 bg-slate-950 border-t border-slate-800 flex items-center justify-between print:hidden">
                      <span className="text-[11px] text-slate-400">
                        Scans Completed: {getMemberScanCount(member)}/3
                      </span>
                      <button
                        onClick={() => handleDownloadBadgePng(member, team)}
                        className="text-xs text-indigo-400 hover:text-indigo-300 font-semibold flex items-center gap-1 cursor-pointer"
                      >
                        <Download className="w-3.5 h-3.5" /> Download PNG
                      </button>
                    </div>
                  </div>
                ))
              )}
            </div>
          </div>
        )}

        {/* ====================================================================
            TAB 3: VOLUNTEER CREDENTIAL MANAGER
           ==================================================================== */}
        {adminTab === 'volunteers' && (
          <div className="grid md:grid-cols-3 gap-6">
            <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 h-fit space-y-4">
              <h2 className="text-base font-bold text-white flex items-center gap-2">
                <KeyRound className="w-4 h-4 text-emerald-400" />
                Create Volunteer Login
              </h2>
              <form onSubmit={handleAddVolunteer} className="space-y-3">
                <div>
                  <label className="block text-xs text-slate-300 mb-1">Volunteer Name & Desk</label>
                  <input
                    type="text"
                    value={newVolName}
                    onChange={(e) => setNewVolName(e.target.value)}
                    placeholder="e.g. Sneha Patel (Gate 2)"
                    className="w-full px-3 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                    required
                  />
                </div>
                <div>
                  <label className="block text-xs text-slate-300 mb-1">Login Username</label>
                  <input
                    type="text"
                    value={newVolUser}
                    onChange={(e) => setNewVolUser(e.target.value)}
                    placeholder="e.g. volunteer3"
                    className="w-full px-3 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                    required
                  />
                </div>
                <div>
                  <label className="block text-xs text-slate-300 mb-1">Login Password</label>
                  <input
                    type="text"
                    value={newVolPass}
                    onChange={(e) => setNewVolPass(e.target.value)}
                    placeholder="e.g. pass123"
                    className="w-full px-3 py-2 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                    required
                  />
                </div>
                <button
                  type="submit"
                  className="w-full py-2.5 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white font-semibold text-xs cursor-pointer"
                >
                  Add Volunteer Account
                </button>
              </form>
            </div>

            <div className="md:col-span-2 bg-slate-900 border border-slate-800 rounded-2xl p-5 space-y-4">
              <h3 className="text-base font-bold text-white">Authorized Volunteer Credentials</h3>
              <div className="space-y-2.5">
                {store.volunteers.map((v) => (
                  <div
                    key={v.id}
                    className="p-3.5 rounded-xl bg-slate-950 border border-slate-800 flex items-center justify-between"
                  >
                    <div>
                      <p className="text-sm font-bold text-white">{v.name}</p>
                      <p className="text-xs font-mono text-emerald-400 mt-0.5">
                        Username: {v.username} • Password: {v.password}
                      </p>
                    </div>
                    <button
                      onClick={() => handleDeleteVolunteer(v.id)}
                      className="p-2 rounded-lg bg-slate-900 hover:bg-rose-950 text-slate-400 hover:text-rose-400 cursor-pointer"
                    >
                      <Trash2 className="w-4 h-4" />
                    </button>
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}

        {/* ====================================================================
            TAB 4: 3-SESSION ATTENDANCE MASTER SHEET & CSV EXPORT
           ==================================================================== */}
        {adminTab === 'reports' && (
          <div className="space-y-6">
            <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 flex flex-wrap items-center justify-between gap-4">
              <div>
                <h2 className="text-lg font-bold text-white">
                  Master 3-Session Attendance Sheet (Day 1 Morning • Day 1 Night • Day 2 Morning)
                </h2>
                <p className="text-xs text-slate-400">
                  Real-time status of every participant across all 3 mandatory QR scans.
                </p>
              </div>
              <button
                onClick={handleExportCsv}
                className="px-4 py-2.5 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white text-xs font-semibold flex items-center gap-2 shadow-lg shadow-emerald-600/20 cursor-pointer"
              >
                <Download className="w-4 h-4" /> Export 3-Round Attendance CSV
              </button>
            </div>

            <div className="bg-slate-900 border border-slate-800 rounded-2xl overflow-x-auto">
              <table className="w-full text-left border-collapse text-xs">
                <thead>
                  <tr className="border-b border-slate-800 bg-slate-950/60 text-slate-400">
                    <th className="p-3.5">Team</th>
                    <th className="p-3.5">Participant Name</th>
                    <th className="p-3.5">Unique QR Code</th>
                    <th className="p-3.5">Scan 1: Day 1 Morning</th>
                    <th className="p-3.5">Scan 2: Day 1 Night</th>
                    <th className="p-3.5">Scan 3: Day 2 Morning</th>
                    <th className="p-3.5 text-center">Total Scans</th>
                  </tr>
                </thead>
                <tbody className="divide-y divide-slate-800/70">
                  {store.teams.flatMap((team) =>
                    team.members.map((m) => {
                      const d1m = m.attendance?.day1_morning;
                      const d1n = m.attendance?.day1_night;
                      const d2m = m.attendance?.day2_morning;
                      const count = getMemberScanCount(m);
                      return (
                        <tr key={m.id} className="hover:bg-slate-800/40">
                          <td className="p-3.5 font-semibold text-slate-200">
                            {team.name}
                            <div className="text-[10px] text-slate-500">{team.bay}</div>
                          </td>
                          <td className="p-3.5 font-bold text-white">
                            {m.name}
                            <div className="text-[10px] text-slate-400 font-normal">{m.role}</div>
                          </td>
                          <td className="p-3.5 font-mono text-indigo-300">{m.qrCode}</td>
                          <td className="p-3.5">
                            {d1m?.present ? (
                              <span className="text-emerald-400 font-semibold">
                                Present ({d1m.timestamp})
                              </span>
                            ) : (
                              <span className="text-slate-500">Pending</span>
                            )}
                          </td>
                          <td className="p-3.5">
                            {d1n?.present ? (
                              <span className="text-emerald-400 font-semibold">
                                Present ({d1n.timestamp})
                              </span>
                            ) : (
                              <span className="text-slate-500">Pending</span>
                            )}
                          </td>
                          <td className="p-3.5">
                            {d2m?.present ? (
                              <span className="text-emerald-400 font-semibold">
                                Present ({d2m.timestamp})
                              </span>
                            ) : (
                              <span className="text-slate-500">Pending</span>
                            )}
                          </td>
                          <td className="p-3.5 text-center">
                            <span
                              className={`px-2.5 py-1 rounded-full font-bold ${
                                count === 3
                                  ? 'bg-emerald-500/20 text-emerald-300 border border-emerald-500/30'
                                  : count > 0
                                  ? 'bg-amber-500/20 text-amber-300 border border-amber-500/30'
                                  : 'bg-slate-800 text-slate-400'
                              }`}
                            >
                              {count} / 3
                            </span>
                          </td>
                        </tr>
                      );
                    })
                  )}
                </tbody>
              </table>
            </div>
          </div>
        )}

        {/* ====================================================================
            TAB 5: HOW TO DEPLOY & USE ON MOBILE PHONES (STEP-BY-STEP GUIDE)
           ==================================================================== */}
        {adminTab === 'deploy' && (
          <div className="space-y-6">
            {/* Top Status & Database Sync Bar */}
            <div className="bg-gradient-to-r from-indigo-950/70 to-slate-900 border border-indigo-500/30 rounded-2xl p-5 flex flex-wrap items-center justify-between gap-4">
              <div className="space-y-1">
                <div className="flex items-center gap-2">
                  <Smartphone className="w-5 h-5 text-indigo-400" />
                  <h2 className="text-lg font-bold text-white">
                    VS Code (`.tsx`) → Vercel → Mobile Phone Deployment Guide
                  </h2>
                  <span
                    className={`text-[11px] px-2.5 py-0.5 rounded-full font-semibold border ${
                      cloudSynced
                        ? 'bg-emerald-500/20 text-emerald-300 border-emerald-500/30'
                        : 'bg-amber-500/20 text-amber-300 border-amber-500/30'
                    }`}
                  >
                    {cloudSynced ? 'Cloud Sync Active' : 'Local Storage Mode'}
                  </span>
                </div>
                <p className="text-xs text-slate-300">
                  This code includes <code className="text-indigo-300 font-mono">// @ts-nocheck</code> at the top so you can paste it directly into <code className="text-indigo-300 font-mono">src/App.tsx</code> without TypeScript build errors on Vercel.
                </p>
              </div>

              <div className="flex flex-wrap items-center gap-2">
                <button
                  onClick={handleExportJsonBackup}
                  className="px-3.5 py-2 rounded-xl bg-slate-800 hover:bg-slate-700 text-xs font-semibold text-white flex items-center gap-1.5 border border-slate-700 cursor-pointer"
                >
                  <Download className="w-3.5 h-3.5 text-indigo-400" /> Export Roster JSON
                </button>
                <label className="px-3.5 py-2 rounded-xl bg-indigo-600 hover:bg-indigo-500 text-xs font-semibold text-white flex items-center gap-1.5 cursor-pointer">
                  <Upload className="w-3.5 h-3.5" /> Import Roster JSON
                  <input
                    type="file"
                    accept=".json"
                    onChange={handleImportJsonBackup}
                    className="hidden"
                  />
                </label>
              </div>
            </div>

            <div className="grid md:grid-cols-2 gap-6">
              {/* Step 1: Create Vite TypeScript Project in VS Code */}
              <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 space-y-4">
                <div className="flex items-center justify-between">
                  <div className="flex items-center gap-2.5">
                    <div className="w-8 h-8 rounded-lg bg-indigo-500/20 border border-indigo-500/30 flex items-center justify-center text-indigo-400 font-bold text-sm">
                      1
                    </div>
                    <div>
                      <h3 className="text-sm font-bold text-white">Create `.tsx` Project in VS Code Terminal</h3>
                      <p className="text-xs text-slate-400">Open VS Code, press Ctrl+` (Terminal), and run:</p>
                    </div>
                  </div>
                </div>

                <div className="bg-slate-950 border border-slate-800 rounded-xl p-3.5 font-mono text-xs text-emerald-300 space-y-1.5 overflow-x-auto">
                  <div>npm create vite@latest hackathon-qr -- --template react-ts</div>
                  <div>cd hackathon-qr</div>
                  <div>npm install lucide-react firebase</div>
                  <div>npm install -D tailwindcss @tailwindcss/vite</div>
                </div>

                <p className="text-xs text-slate-300 leading-relaxed">
                  Next, open the <code className="px-1.5 py-0.5 rounded bg-slate-950 text-indigo-300 font-mono">hackathon-qr</code> folder in VS Code.
                </p>
              </div>

              {/* Step 2: Configure Tailwind & Paste into src/App.tsx */}
              <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 space-y-4">
                <div className="flex items-center gap-2.5">
                  <div className="w-8 h-8 rounded-lg bg-purple-500/20 border border-purple-500/30 flex items-center justify-center text-purple-400 font-bold text-sm">
                    2
                  </div>
                  <div>
                    <h3 className="text-sm font-bold text-white">Paste Code into `src/App.tsx` & Enable Tailwind</h3>
                    <p className="text-xs text-slate-400">Update these 3 files inside your VS Code project:</p>
                  </div>
                </div>

                <div className="bg-slate-950 border border-slate-800 rounded-xl p-3.5 font-mono text-xs text-slate-300 space-y-2 overflow-x-auto">
                  <div className="text-indigo-300 font-bold">// 1. vite.config.ts</div>
                  <div>import &#123; defineConfig &#125; from 'vite'</div>
                  <div>import react from '@vitejs/plugin-react'</div>
                  <div>import tailwindcss from '@tailwindcss/vite'</div>
                  <div>export default defineConfig(&#123; plugins: [react(), tailwindcss()] &#125;)</div>
                  <div className="text-indigo-300 font-bold pt-2">// 2. src/index.css (Replace entire file with:)</div>
                  <div className="text-emerald-300">@import "tailwindcss";</div>
                  <div className="text-indigo-300 font-bold pt-2">// 3. src/App.tsx</div>
                  <div>Paste the entire code from this editor into src/App.tsx and save (Ctrl+S).</div>
                </div>
              </div>

              {/* Step 3: Deploy to Vercel */}
              <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 space-y-4">
                <div className="flex items-center gap-2.5">
                  <div className="w-8 h-8 rounded-lg bg-emerald-500/20 border border-emerald-500/30 flex items-center justify-center text-emerald-400 font-bold text-sm">
                    3
                  </div>
                  <div>
                    <h3 className="text-sm font-bold text-white">Deploy to Vercel (HTTPS Link for Phone Camera)</h3>
                    <p className="text-xs text-slate-400">Run right inside your VS Code terminal</p>
                  </div>
                </div>

                <div className="bg-slate-950 border border-slate-800 rounded-xl p-3.5 font-mono text-xs text-emerald-300 space-y-1.5 overflow-x-auto">
                  <div># Test locally first:</div>
                  <div>npm run dev</div>
                  <div className="pt-2"># Deploy live to Vercel in 1 command:</div>
                  <div>npx vercel --prod</div>
                </div>

                <p className="text-xs text-slate-300 leading-relaxed">
                  Log in when prompted and press Enter for all default settings. Vercel will output a live{' '}
                  <code className="px-1.5 py-0.5 rounded bg-slate-950 text-emerald-300 font-mono">
                    https://hackathon-qr-xyz.vercel.app
                  </code>{' '}
                  URL.
                </p>
              </div>

              {/* Step 4: Use on Mobile Phones & Multi-Device Sync */}
              <div className="bg-slate-900 border border-slate-800 rounded-2xl p-5 space-y-4">
                <div className="flex items-center gap-2.5">
                  <div className="w-8 h-8 rounded-lg bg-amber-500/20 border border-amber-500/30 flex items-center justify-center text-amber-400 font-bold text-sm">
                    4
                  </div>
                  <div>
                    <h3 className="text-sm font-bold text-white">Use on Phones (Camera & Multi-Phone Sync)</h3>
                    <p className="text-xs text-slate-400">Scanning physical ID cards at your venue</p>
                  </div>
                </div>

                <ul className="space-y-2 text-xs text-slate-300">
                  <li className="flex items-start gap-2">
                    <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0 mt-0.5" />
                    <span>
                      <strong>Open on Phone:</strong> Send the <code className="text-emerald-300 font-mono">https://...vercel.app</code> link to volunteers via WhatsApp. Tap <strong>Volunteer Login</strong> → Select Team → Select Member → Tap <strong>Open Camera Scanner</strong> and click <strong>Allow Camera</strong>.
                    </span>
                  </li>
                  <li className="flex items-start gap-2">
                    <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0 mt-0.5" />
                    <span>
                      <strong>Add to Home Screen:</strong> On Android Chrome or iOS Safari, tap <em>Share / Menu → Add to Home Screen</em> so volunteers can use it like a native full-screen app.
                    </span>
                  </li>
                  <li className="flex items-start gap-2">
                    <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0 mt-0.5" />
                    <span>
                      <strong>Sync Across Multiple Phones:</strong> Either use the <strong>Export / Import Roster JSON</strong> buttons above to share the pre-loaded team list, or paste your Firebase project config into <code className="text-indigo-300 font-mono">firebaseConfig</code> at the top of <code className="text-indigo-300 font-mono">src/App.tsx</code> for automatic real-time cloud sync across all phones.
                    </span>
                  </li>
                </ul>
              </div>
            </div>
          </div>
        )}
      </main>
    </div>
  );
}