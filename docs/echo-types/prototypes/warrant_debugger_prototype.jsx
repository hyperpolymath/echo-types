// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

import React, { useMemo, useState } from "react";
import { motion } from "framer-motion";
import { Play, RotateCcw, AlertTriangle, GitBranch, Sigma, ShieldCheck } from "lucide-react";
import { Card, CardContent } from "@/components/ui/card";
import { Button } from "@/components/ui/button";

const repairs = {
  contradiction: {
    label: "No repair",
    status: "Contradictory Fibre",
    tone: "border-red-400/50 bg-red-950/20 text-red-100",
    cost: "NONE",
    formula: "Echo_S = Σ p:P · Cˡⁱⁿᵉᵃʳ_inst(p) × Cᵃᶠᶠⁱⁿᵉ_ice(p) = ∅",
    explanation:
      "No prior state satisfies the active proof obligations. The minimal unsatisfiable core is Instrumental Linear × Ice Core Affine.",
    fibre: { x: 205, y: 118, w: 0, h: 0, opacity: 0 },
    showBridge: false,
  },
  relaxInstrumental: {
    label: "Relax Instrumental",
    status: "Fibre Restored (Weakened)",
    tone: "border-amber-300/50 bg-amber-950/20 text-amber-100",
    cost: "LOW–MEDIUM",
    formula: "Echo_S = Σ p:P · Cᵃᶠᶠⁱⁿᵉ_inst(p) × Cᵃᶠᶠⁱⁿᵉ_ice(p)",
    explanation:
      "Compatibility restored under the weakened Relax Instrumental warrant. A non-empty fibre has been re-established, but one proof obligation has been destroyed.",
    fibre: { x: 220, y: 112, w: 58, h: 34, opacity: 1 },
    showBridge: true,
  },
  widenIce: {
    label: "Widen Ice Core Bound",
    status: "Fibre Restored (Interval)",
    tone: "border-amber-300/50 bg-amber-950/20 text-amber-100",
    cost: "MEDIUM",
    formula: "Echo_S = Σ p:P · Cˡⁱⁿᵉᵃʳ_inst(p) × Cⁱⁿᵗᵉʳᵛᵃˡ_ice(p)",
    explanation:
      "Compatibility restored by widening the Ice Core calibration interval. The contradiction was dependent on an overly narrow proxy bound.",
    fibre: { x: 210, y: 118, w: 42, h: 24, opacity: 1 },
    showBridge: true,
  },
  softMode: {
    label: "Switch to Soft Mode",
    status: "Weighted Support Field",
    tone: "border-sky-300/50 bg-sky-950/20 text-sky-100",
    cost: "HIGH",
    formula: "w_S(p) = π(p) · L_inst(p) · L_ice(p)",
    explanation:
      "Hard compatibility has been replaced by a likelihood field. This avoids empty fibres, but no longer proves strict joint satisfiability.",
    fibre: { x: 175, y: 92, w: 125, h: 76, opacity: 0.75 },
    showBridge: false,
  },
};

const strategyOrder = ["contradiction", "relaxInstrumental", "widenIce", "softMode"];

function Badge({ children, className = "" }) {
  return <span className={`rounded-full px-2 py-1 text-xs font-medium ${className}`}>{children}</span>;
}

function ShapePanel({ state }) {
  const repair = repairs[state];
  const isSoft = state === "softMode";

  return (
    <div className="relative mx-auto aspect-[1.42/1] w-full max-w-2xl overflow-hidden rounded-2xl border border-zinc-800 bg-zinc-950 shadow-2xl">
      <svg viewBox="0 0 520 365" className="h-full w-full">
        <defs>
          <filter id="glowBlue" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="5" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <filter id="glowGreen" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="5" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <radialGradient id="softHeat" cx="50%" cy="50%" r="60%">
            <stop offset="0%" stopColor="white" stopOpacity="0.85" />
            <stop offset="42%" stopColor="#fbbf24" stopOpacity="0.45" />
            <stop offset="100%" stopColor="#38bdf8" stopOpacity="0" />
          </radialGradient>
        </defs>

        <rect x="48" y="44" width="424" height="292" fill="none" stroke="#27272a" strokeDasharray="5 6" />
        <text x="58" y="62" fill="#fafafa" fontSize="10" fontWeight="700">Total Parameter Space P</text>

        <motion.rect
          x={84}
          y={86}
          width={154}
          height={103}
          rx={0}
          fill="#2563eb"
          fillOpacity={state === "relaxInstrumental" || state === "softMode" ? 0.28 : 0.2}
          stroke="#60a5fa"
          strokeWidth={state === "contradiction" ? 3 : 2}
          strokeDasharray={state === "contradiction" ? "5 5" : "0"}
          filter="url(#glowBlue)"
          animate={{ x: state === "relaxInstrumental" || state === "softMode" ? 138 : 84, width: state === "relaxInstrumental" ? 145 : 154 }}
          transition={{ type: "spring", stiffness: 80, damping: 18 }}
        />
        <text x="114" y="78" fill="#fafafa" fontSize="10" fontWeight="700">Instrumental {state === "contradiction" ? "(Linear)" : state === "softMode" ? "(Likelihood)" : "(Affine)"}</text>

        <motion.polygon
          points="296,86 442,86 410,188 258,188"
          fill="#22c55e"
          fillOpacity={state === "widenIce" || state === "softMode" ? 0.3 : 0.18}
          stroke="#86efac"
          strokeWidth={state === "widenIce" ? 3 : 2.5}
          filter="url(#glowGreen)"
          animate={{ opacity: 1 }}
        />
        <text x="310" y="78" fill="#fafafa" fontSize="10" fontWeight="700">Ice Core {state === "widenIce" ? "(Interval)" : state === "softMode" ? "(Likelihood)" : "(Affine)"}</text>

        <polygon points="238,210 283,223 318,253 282,281 236,295 228,253" fill="#f59e0b" fillOpacity="0.08" stroke="#f59e0b" strokeOpacity="0.3" strokeWidth="2" />
        <text x="223" y="322" fill="#71717a" fontSize="10">Tree Ring (inactive)</text>

        {repair.showBridge && (
          <motion.path
            d="M 229 140 C 248 128, 264 130, 281 144"
            fill="none"
            stroke="#fbbf24"
            strokeWidth="2"
            strokeDasharray="4 5"
            initial={{ pathLength: 0, opacity: 0 }}
            animate={{ pathLength: 1, opacity: 0.95 }}
            transition={{ duration: 0.7 }}
          />
        )}

        {isSoft ? (
          <motion.ellipse
            cx="240"
            cy="132"
            rx={repair.fibre.w}
            ry={repair.fibre.h}
            fill="url(#softHeat)"
            initial={{ opacity: 0 }}
            animate={{ opacity: repair.fibre.opacity }}
            transition={{ duration: 0.45 }}
          />
        ) : (
          <motion.rect
            x={repair.fibre.x}
            y={repair.fibre.y}
            width={repair.fibre.w}
            height={repair.fibre.h}
            rx="9"
            fill="#fef3c7"
            fillOpacity="0.9"
            stroke="#fde68a"
            strokeWidth="2"
            initial={false}
            animate={repair.fibre}
            transition={{ type: "spring", stiffness: 100, damping: 18 }}
          />
        )}

        {state === "contradiction" && (
          <motion.g initial={{ opacity: 0, scale: 0.92 }} animate={{ opacity: 1, scale: 1 }}>
            <line x1="242" y1="119" x2="270" y2="147" stroke="#fb7185" strokeWidth="3" />
            <line x1="270" y1="119" x2="242" y2="147" stroke="#fb7185" strokeWidth="3" />
            <text x="190" y="168" fill="#fecdd3" fontSize="12" fontWeight="700">∅ minimal unsatisfiable core</text>
          </motion.g>
        )}
      </svg>
    </div>
  );
}

function ProofStepper({ state, setState }) {
  const currentIndex = strategyOrder.indexOf(state);

  return (
    <div className="space-y-3">
      <div className="flex items-center justify-between gap-3">
        <div>
          <p className="text-sm font-semibold text-zinc-200">Diagnostic sequence</p>
          <p className="text-xs text-zinc-500">Isolate → weaken → recompute → disclose cost</p>
        </div>
        <div className="flex gap-2">
          <Button
            variant="secondary"
            size="icon"
            className="rounded-full bg-zinc-800 text-zinc-100 hover:bg-zinc-700"
            onClick={() => setState(strategyOrder[Math.min(currentIndex + 1, strategyOrder.length - 1)])}
          >
            <Play className="h-4 w-4" />
          </Button>
          <Button
            variant="secondary"
            size="icon"
            className="rounded-full bg-zinc-800 text-zinc-100 hover:bg-zinc-700"
            onClick={() => setState("contradiction")}
          >
            <RotateCcw className="h-4 w-4" />
          </Button>
        </div>
      </div>
      <div className="grid grid-cols-4 gap-2">
        {strategyOrder.map((key, index) => (
          <button
            key={key}
            onClick={() => setState(key)}
            className={`rounded-xl border p-2 text-left text-xs transition ${
              key === state ? "border-zinc-100 bg-zinc-800 text-white" : "border-zinc-800 bg-zinc-950 text-zinc-500 hover:border-zinc-600"
            }`}
          >
            <div className="mb-1 font-semibold">{index + 1}. {repairs[key].label}</div>
            <div>{repairs[key].cost}</div>
          </button>
        ))}
      </div>
    </div>
  );
}

export default function WarrantDebuggerPrototype() {
  const [state, setState] = useState("contradiction");
  const repair = repairs[state];

  const volume = useMemo(() => {
    if (state === "contradiction") return "0.0%";
    if (state === "relaxInstrumental") return "8.4%";
    if (state === "widenIce") return "5.7%";
    return "effective support: 23.1%";
  }, [state]);

  return (
    <main className="min-h-screen bg-black p-4 text-zinc-100 sm:p-8">
      <div className="mx-auto max-w-5xl space-y-6">
        <header className="flex flex-col gap-4 sm:flex-row sm:items-start sm:justify-between">
          <div>
            <div className="mb-3 flex items-center gap-2 text-sm text-amber-200">
              <GitBranch className="h-4 w-4" />
              Warrant Debugger
            </div>
            <h1 className="text-3xl font-semibold tracking-tight">Contradiction as a Proof Event</h1>
            <p className="mt-2 max-w-3xl text-sm leading-6 text-zinc-400">
              The debugger begins with an empty fibre. Repairs are not silent fixes; each one weakens, widens, or replaces a proof obligation and reports the epistemic cost.
            </p>
          </div>
          <Badge className={repair.tone}>{repair.status}</Badge>
        </header>

        <ShapePanel state={state} />

        <ProofStepper state={state} setState={setState} />

        <Card className={`rounded-2xl border ${repair.tone}`}>
          <CardContent className="grid gap-5 p-5 md:grid-cols-[1.25fr_0.75fr]">
            <div className="space-y-3">
              <div className="flex items-center gap-2">
                {state === "contradiction" ? <AlertTriangle className="h-5 w-5" /> : <ShieldCheck className="h-5 w-5" />}
                <h2 className="text-lg font-semibold">{repair.status}</h2>
              </div>
              <p className="text-sm leading-6 text-zinc-300">{repair.explanation}</p>
              <div className="rounded-xl border border-zinc-700 bg-black/45 p-3 font-mono text-xs text-zinc-200">
                {repair.formula}
              </div>
            </div>
            <div className="grid grid-cols-2 gap-3 md:grid-cols-1">
              <div className="rounded-xl border border-zinc-700 bg-black/35 p-4">
                <div className="mb-1 flex items-center gap-2 text-xs uppercase tracking-wide text-zinc-500"><Sigma className="h-3.5 w-3.5" />Uncertainty</div>
                <div className="text-2xl font-semibold">{volume}</div>
              </div>
              <div className="rounded-xl border border-zinc-700 bg-black/35 p-4">
                <div className="mb-1 text-xs uppercase tracking-wide text-zinc-500">Epistemic cost</div>
                <div className="text-2xl font-semibold">{repair.cost}</div>
              </div>
            </div>
          </CardContent>
        </Card>

        <section className="grid gap-4 md:grid-cols-3">
          <Card className="rounded-2xl border-zinc-800 bg-zinc-950">
            <CardContent className="p-4">
              <h3 className="mb-2 font-semibold">Minimal unsat core</h3>
              <p className="text-sm text-zinc-400">The contradiction is localized before any repair is proposed.</p>
            </CardContent>
          </Card>
          <Card className="rounded-2xl border-zinc-800 bg-zinc-950">
            <CardContent className="p-4">
              <h3 className="mb-2 font-semibold">Typed relaxation</h3>
              <p className="text-sm text-zinc-400">Linear → Affine is allowed only when the hierarchy proves inclusion.</p>
            </CardContent>
          </Card>
          <Card className="rounded-2xl border-zinc-800 bg-zinc-950">
            <CardContent className="p-4">
              <h3 className="mb-2 font-semibold">Provenance retained</h3>
              <p className="text-sm text-zinc-400">The restored fibre remains marked as weakened, not cleanly proven.</p>
            </CardContent>
          </Card>
        </section>
      </div>
    </main>
  );
}
