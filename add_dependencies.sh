#!/bin/bash
# Add blocked-by dependencies between issues
set -e

REPO="konard/physical-unified-theory"
ISSUE_MAP_FILE="/tmp/gh-issue-solver-1773894909440/issue_map.txt"

get_issue_id() {
    local num="$1"
    gh api graphql -f query="{ repository(owner: \"konard\", name: \"physical-unified-theory\") { issue(number: $num) { id } } }" --jq '.data.repository.issue.id'
}

add_blocked_by() {
    local issue_num="$1"
    local blocking_num="$2"
    local issue_id=$(get_issue_id "$issue_num")
    local blocking_id=$(get_issue_id "$blocking_num")
    local result=$(gh api graphql -f query="mutation { addBlockedBy(input: { issueId: \"$issue_id\", blockingIssueId: \"$blocking_id\" }) { issue { id } } }" 2>&1)
    if echo "$result" | grep -q '"errors"'; then
        echo "  WARN: $blocking_num blocks $issue_num - $(echo $result | grep -oP '"message":"[^"]*"' | head -1)"
    else
        echo "  OK: #$blocking_num blocks #$issue_num"
    fi
}

get_mapping() {
    local key="$1"
    grep "^${key}=" "$ISSUE_MAP_FILE" | head -1 | cut -d= -f2
}

# Read mappings
A=$(get_mapping "A"); B=$(get_mapping "B"); C=$(get_mapping "C"); D=$(get_mapping "D")
E=$(get_mapping "E"); F=$(get_mapping "F"); G=$(get_mapping "G"); H=$(get_mapping "H")
I=$(get_mapping "I"); J=$(get_mapping "J"); K=$(get_mapping "K"); L=$(get_mapping "L")
M=$(get_mapping "M"); N=$(get_mapping "N"); O=$(get_mapping "O")

A1=$(get_mapping "A.1"); A2=$(get_mapping "A.2"); A3=$(get_mapping "A.3")
A4=$(get_mapping "A.4"); A5=$(get_mapping "A.5"); A6=$(get_mapping "A.6")
B1=$(get_mapping "B.1"); B2=$(get_mapping "B.2"); B3=$(get_mapping "B.3")
B4=$(get_mapping "B.4"); B5=$(get_mapping "B.5"); B6=$(get_mapping "B.6")
B7=$(get_mapping "B.7"); B89=$(get_mapping "B.89")
C1=$(get_mapping "C.1"); C2=$(get_mapping "C.2"); C3=$(get_mapping "C.3")
C4=$(get_mapping "C.4"); C5=$(get_mapping "C.5"); C6=$(get_mapping "C.6")
C7=$(get_mapping "C.7"); C8=$(get_mapping "C.8"); C9=$(get_mapping "C.9")
C10=$(get_mapping "C.10")
D1=$(get_mapping "D.1"); D2=$(get_mapping "D.2"); D3=$(get_mapping "D.3")
D4=$(get_mapping "D.4"); D5=$(get_mapping "D.5"); D6=$(get_mapping "D.6")
D7=$(get_mapping "D.7"); D8=$(get_mapping "D.8"); D910=$(get_mapping "D.910")
E1=$(get_mapping "E.1"); E2=$(get_mapping "E.2"); E3=$(get_mapping "E.3")
E4=$(get_mapping "E.4"); E58=$(get_mapping "E.58")
F1=$(get_mapping "F.1"); F2=$(get_mapping "F.2"); F3=$(get_mapping "F.3")
F4=$(get_mapping "F.4"); F5=$(get_mapping "F.5"); F6=$(get_mapping "F.6")
F7=$(get_mapping "F.7")
G1=$(get_mapping "G.1"); G2=$(get_mapping "G.2"); G3=$(get_mapping "G.3")
G4=$(get_mapping "G.4"); G59=$(get_mapping "G.59")
H1=$(get_mapping "H.1"); H2=$(get_mapping "H.2"); H3=$(get_mapping "H.3")
H4=$(get_mapping "H.4"); H5=$(get_mapping "H.5"); H68=$(get_mapping "H.68")
I1=$(get_mapping "I.1"); I2=$(get_mapping "I.2"); I3=$(get_mapping "I.3")
I45=$(get_mapping "I.45"); I6=$(get_mapping "I.6"); I7=$(get_mapping "I.7")
J1=$(get_mapping "J.1"); J2=$(get_mapping "J.2"); J3=$(get_mapping "J.3")
J4=$(get_mapping "J.4"); J59=$(get_mapping "J.59")
K0=$(get_mapping "K.0"); K1=$(get_mapping "K.1"); K2=$(get_mapping "K.2")
K35=$(get_mapping "K.35"); K612=$(get_mapping "K.612")
L1=$(get_mapping "L.1"); L2=$(get_mapping "L.2"); L35=$(get_mapping "L.35")
L610=$(get_mapping "L.610")
M1=$(get_mapping "M.1"); M2=$(get_mapping "M.2"); M36=$(get_mapping "M.36")
M711=$(get_mapping "M.711")
N1=$(get_mapping "N.1"); N2=$(get_mapping "N.2"); N35=$(get_mapping "N.35")
N610=$(get_mapping "N.610")
O1=$(get_mapping "O.1"); O2=$(get_mapping "O.2"); O3=$(get_mapping "O.3")
O49=$(get_mapping "O.49")

echo "=== Track-level dependencies ==="

# Note: B already blocked by A (done in test), skip that one
# B blocked by A - already done
# C blocked by A
add_blocked_by "$C" "$A"
# D blocked by A and B
add_blocked_by "$D" "$A"
add_blocked_by "$D" "$B"
# E blocked by A, C, D
add_blocked_by "$E" "$A"
add_blocked_by "$E" "$C"
add_blocked_by "$E" "$D"
# F blocked by A, B, C
add_blocked_by "$F" "$A"
add_blocked_by "$F" "$B"
add_blocked_by "$F" "$C"
# G blocked by D, E, F
add_blocked_by "$G" "$D"
add_blocked_by "$G" "$E"
add_blocked_by "$G" "$F"
# H blocked by A, C
add_blocked_by "$H" "$A"
add_blocked_by "$H" "$C"
# I blocked by A, C, F
add_blocked_by "$I" "$A"
add_blocked_by "$I" "$C"
add_blocked_by "$I" "$F"
# J blocked by E
add_blocked_by "$J" "$E"
# K blocked by A, C, D, E
add_blocked_by "$K" "$A"
add_blocked_by "$K" "$C"
add_blocked_by "$K" "$D"
add_blocked_by "$K" "$E"
# L blocked by A, C, D, E
add_blocked_by "$L" "$A"
add_blocked_by "$L" "$C"
add_blocked_by "$L" "$D"
add_blocked_by "$L" "$E"
# O blocked by C, D
add_blocked_by "$O" "$C"
add_blocked_by "$O" "$D"

echo ""
echo "=== Sub-issue level dependencies ==="

# B sub-issues
add_blocked_by "$B1" "$A1"
add_blocked_by "$B1" "$A2"
add_blocked_by "$B2" "$B1"
add_blocked_by "$B3" "$B2"
add_blocked_by "$B4" "$B3"
add_blocked_by "$B6" "$B2"
add_blocked_by "$B5" "$B6"

# C sub-issues
add_blocked_by "$C1" "$A1"
add_blocked_by "$C1" "$A5"
add_blocked_by "$C2" "$C1"
add_blocked_by "$C3" "$C1"
add_blocked_by "$C4" "$C2"
add_blocked_by "$C5" "$C4"
add_blocked_by "$C6" "$C1"
add_blocked_by "$C7" "$C6"
add_blocked_by "$C8" "$C1"
add_blocked_by "$C9" "$C1"

# D sub-issues
add_blocked_by "$D1" "$A2"
add_blocked_by "$D2" "$D1"
add_blocked_by "$D2" "$A2"
add_blocked_by "$D3" "$D2"
add_blocked_by "$D3" "$B2"
add_blocked_by "$D3" "$B3"
add_blocked_by "$D4" "$D3"
add_blocked_by "$D5" "$D3"
add_blocked_by "$D6" "$D3"
add_blocked_by "$D7" "$D3"
add_blocked_by "$D8" "$D4"

# E sub-issues
add_blocked_by "$E1" "$C1"
add_blocked_by "$E1" "$C9"
add_blocked_by "$E1" "$D1"
add_blocked_by "$E2" "$E1"
add_blocked_by "$E3" "$E2"
add_blocked_by "$E4" "$E3"

# F sub-issues
add_blocked_by "$F1" "$A1"
add_blocked_by "$F1" "$A5"
add_blocked_by "$F1" "$B7"
add_blocked_by "$F2" "$F1"
add_blocked_by "$F2" "$C1"
add_blocked_by "$F3" "$F2"
add_blocked_by "$F4" "$F1"
add_blocked_by "$F5" "$F2"
add_blocked_by "$F6" "$D8"
add_blocked_by "$F7" "$D3"

# G sub-issues
add_blocked_by "$G1" "$D3"
add_blocked_by "$G1" "$D4"
add_blocked_by "$G1" "$F1"
add_blocked_by "$G2" "$G1"
add_blocked_by "$G3" "$G1"
add_blocked_by "$G4" "$G1"

# H sub-issues
add_blocked_by "$H1" "$A1"
add_blocked_by "$H1" "$C1"
add_blocked_by "$H2" "$H1"
add_blocked_by "$H3" "$H1"
add_blocked_by "$H4" "$H3"
add_blocked_by "$H5" "$C6"

# I sub-issues
add_blocked_by "$I1" "$C9"
add_blocked_by "$I1" "$F2"
add_blocked_by "$I2" "$I1"
add_blocked_by "$I3" "$I1"
add_blocked_by "$I6" "$I1"
add_blocked_by "$I7" "$I6"

# J sub-issues
add_blocked_by "$J1" "$E3"
add_blocked_by "$J1" "$E4"
add_blocked_by "$J2" "$J1"
add_blocked_by "$J3" "$E4"
add_blocked_by "$J4" "$J3"

# K sub-issues
add_blocked_by "$K0" "$C1"
add_blocked_by "$K0" "$D3"
add_blocked_by "$K0" "$E1"
add_blocked_by "$K1" "$K0"
add_blocked_by "$K1" "$D6"
add_blocked_by "$K2" "$K0"
add_blocked_by "$K2" "$E3"

# L sub-issues
add_blocked_by "$L1" "$E1"
add_blocked_by "$L2" "$A3"

# N sub-issues
add_blocked_by "$N1" "$A1"

# O sub-issues
add_blocked_by "$O1" "$C1"
add_blocked_by "$O2" "$C1"
add_blocked_by "$O3" "$C6"

echo ""
echo "=== Dependencies complete ==="
