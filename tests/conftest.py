def accepts_from_manifest(manifest, word):
    alphabet = {
        item["python_repr"]: item["id"]
        for item in manifest["alphabet"]
    }

    outgoing = {}
    for edge in manifest["transitions"]:
        outgoing.setdefault(
            (edge["source"], edge["symbol"]), set()
        ).add(edge["target"])

    epsilon_outgoing = {}
    for edge in manifest.get("epsilon_transitions", []):
        epsilon_outgoing.setdefault(edge["source"], set()).add(edge["target"])

    def epsilon_closure(states):
        reached = set(states)
        pending = list(states)

        while pending:
            state = pending.pop()
            for target in epsilon_outgoing.get(state, set()):
                if target not in reached:
                    reached.add(target)
                    pending.append(target)

        return reached

    current = epsilon_closure(manifest["start_state_ids"])

    for token in word:
        key = repr(getattr(token, "value", token))
        if key not in alphabet:
            return False

        symbol_id = alphabet[key]
        next_states = set()

        for state in current:
            next_states.update(outgoing.get((state, symbol_id), set()))

        current = epsilon_closure(next_states)

    return bool(current.intersection(manifest["final_state_ids"]))
