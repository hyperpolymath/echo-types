/* Standard Operating Psychopathy — configuration & static data. */
window.SOP = window.SOP || {};

SOP.TILE = 26;                 // pixel size of one tile (base)
SOP.TICK_MS = 250;             // simulation tick
SOP.EVAL_MS = 1000;            // utility re-evaluation interval
SOP.DAY_TICKS = 240;           // ticks per TAG
SOP.START_DAY = 3689;          // days since surface collapse

SOP.GRID_W = 34;
SOP.GRID_H = 22;
SOP.DIG_TOP = 5;               // rows 0..4 stay bedrock
SOP.LINK_RANGE = 8;            // max wire length between nodes (tiles)

SOP.RES = { beton: 220, metall: 80, rationen: 110, oel: 220 };

SOP.MAX_POWER = 600;
SOP.MAX_O2 = 250;

SOP.NEEDS = ['stress', 'hunger', 'exhaustion', 'paranoia', 'o2'];

/* Object definitions. watts>0 = consumer, watts<0 = generator. */
SOP.OBJ = {
  dynamo:    { label: 'TRETBAR-DYNAMO',   watts: -60, icon: '◉', hotkey: '1', cost: { metall: 12 },
               hint: 'Handkurbel. −60 W solange ein Subjekt kurbelt.' },
  lamp:      { label: 'LAMPE',            watts:  12, icon: '✶', hotkey: '2', cost: { metall: 4 },
               hint: 'Beleuchtet Radius 4. Gegen Dunkel-Panik. 12 W.' },
  bed:       { label: 'PRITSCHE',         watts:   0, icon: '▭', hotkey: '3', cost: { metall: 4, beton: 2 },
               hint: 'Schlafplatz. Baut Erschöpfung ab.' },
  dispenser: { label: 'RATIONEN-AUSGABE', watts:   5, icon: '▦', hotkey: '4', cost: { metall: 8 },
               hint: 'Gibt 1 RATION pro Mahlzeit aus. Braucht Strom.' },
  scrubber:  { label: 'LUFT-WÄSCHER',     watts:  25, icon: '≋', hotkey: '5', cost: { metall: 10, beton: 4 },
               hint: 'Zieht Giftgas ab, gibt O₂ aus. 25 W.' },
  generator: { label: 'NOTSTROMAGGREGAT', watts: -100, icon: '▣', hotkey: '6', cost: { metall: 20 },
               hint: '−100 W. Verbrennt 1 ÖL alle 35 s. Öl kommt aus dem Erdreich.' },
  door:      { label: 'SCHOTT',           watts:  10, icon: '╫', hotkey: '7', cost: { metall: 8, beton: 2 },
               hint: 'Blockiert Weg, solange stromlos. Sensor kann es koppeln.' },
  battery:   { label: 'AKKU-BLOCK',       watts:   0, icon: '▮', hotkey: '9', cost: { metall: 14 },
               hint: 'Speichert Überschuss (2000), deckt Spitzen. Gegen Flackerlicht.' },
  farm:      { label: 'PILZFARM',         watts:  15, icon: '✿', hotkey: '0', cost: { beton: 6, metall: 6 },
               hint: 'Züchtet Rationen aus der Wandfeuchte. +1 RATION pro 30 s Strom.' },
  airlock:   { label: 'LUFTSCHLEUSE',     watts:   0, icon: '⌂', hotkey: 'q', cost: { metall: 15, beton: 10 },
               hint: 'Durchbruch zur Oberfläche. Startpunkt für Expeditionen & Neuzugänge. Nur an der Decke.' },
  radio:     { label: 'FUNKTURM',         watts:  30, icon: '⌁', hotkey: 'f', cost: { metall: 18 },
               hint: 'Sendet auf allen Bändern. Verdoppelt die Rate der Neuzugänge. 30 W.' },
  sensor:    { label: 'BEWEGUNGSSENSOR',  watts:   5, icon: '◎', hotkey: '8', cost: { metall: 6 },
               hint: 'Meldet Subjekte im Radius 2. Koppelbar an Schott.' },
  gas_vent:  { label: 'GAS-SCHLOT',       watts:   0, icon: '▲', hotkey: '',  cost: {},
               hint: 'Leckt Giftgas. Einmauern oder waschen.' },
};
SOP.WALL_COST = { beton: 4 };
SOP.BUILDABLE = ['dynamo', 'lamp', 'bed', 'dispenser', 'scrubber', 'generator', 'door', 'sensor', 'battery', 'farm', 'airlock', 'radio'];
SOP.BATTERY_CAP = 2000;
SOP.FARM_TICKS = 120;          // powered ticks per ration grown

/* Colony growth & surface operations. */
SOP.MAX_INMATES = 6;
SOP.EXPEDITION_TICKS = [500, 800];   // duration range while outside
SOP.EXPEDITION_INJURY_CHANCE = 0.18;
SOP.ARRIVAL_BASE = [2600, 3800];     // ticks until a newcomer (no radio)
SOP.ARRIVAL_RADIO = [1300, 1900];    // ... with a powered Funkturm
SOP.LOOT = [
  { res: 'oel',      n: [6, 14], label: 'ÖL-FÄSSER',    weight: 30 },
  { res: 'rationen', n: [5, 10], label: 'KONSERVEN',    weight: 30 },
  { res: 'metall',   n: [6, 12], label: 'SCHROTT',      weight: 22 },
  { res: 'beton',    n: [8, 16], label: 'TRÜMMERSTEINE', weight: 18 },
];

/* Digging outcomes. */
SOP.DIG_TICKS = 4;
SOP.DIG_CACHE_CHANCE = 0.30;
SOP.DIG_GAS_CHANCE = 0.12;
SOP.CACHES = [
  { res: 'rationen', n: [3, 7],  label: 'RATIONEN-DEPOT', weight: 35 },
  { res: 'oel',      n: [7, 12], label: 'ÖL-FLASCH',      weight: 28 },
  { res: 'metall',   n: [4, 9],  label: 'METALL-CACHE',   weight: 22 },
  { res: 'beton',    n: [5, 12], label: 'BETON-CACHE',    weight: 18 },
];

SOP.NAMES = [
  'SUBJEKT-402','SUBJEKT-117','SUBJEKT-774','SUBJEKT-033','SUBJEKT-666',
  'SUBJEKT-291','SUBJEKT-508','SUBJEKT-815','SUBJEKT-149','SUBJEKT-904',
];

SOP.TRAITS = {
  Pyromane:        'Leitet bei Stress Kurzschlüsse ein.',
  Paranoid:        'Panik in Dunkelheit. Hoher Argwohn.',
  Befehlsfixiert:  'Arbeitet stur weiter. Ignoriert Warnlampen.',
  Schlafwandler:   'Wandert nachts. Pennt überall.',
};

SOP.QUAKE_NAMES = ['ERDBEBEN 1', 'ERDBEBEN 2', 'DER MUSSOLINI', 'GOLDENES SPIELZEUG', 'KALTES KLARWASSER', 'MAIKÄFER FLIEG'];

SOP.TICKER_LINES = [
  'JEDER ATEMZUG WIRD REGISTRIERT',
  'VERLASS DEINEN SEKTOR NICHT',
  'DER MUSSOLINI DREHT SICH',
  'KALTES KLARWASSER IST KEIN SPIEL',
  'GOLDENES SPIELZEUG WIRD KONFISZIERT',
  'ARBEIT MACHT ATEM',
  'GEBORGENHEIT IST PFLICHT',
  'HALTE DEIN SCHOTT GESCHLOSSEN',
  'DIE OBERFLÄCHE IST KEIN ORT MEHR',
  'EIN NEUES DEUTSCHES WUNDER: DIE WÄSCHER',
  'ANGST IST ENERGIE. SPAREN SIE DAMIT',
  'WIR WOLLEN WOLLEN. SIE WOLLEN AUCH',
];
