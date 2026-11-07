def accepts_from_manifest(manifest, word):
    alphabet = {item["python_repr"]: item["id"] for item in manifest["alphabet"]}
    outgoing = {}
    for edge in manifest["transitions"]:
        outgoing.setdefault((edge["source"], edge["symbol"]), set()).add(edge["target"])

    current = set(manifest["start_state_ids"])
    for token in word:
        key = repr(getattr(token, "value", token))
        if key not in alphabet:
            return False
        symbol_id = alphabet[key]
        current = set().union(*(outgoing.get((state, symbol_id), set()) for state in current))
    return bool(current.intersection(manifest["final_state_ids"]))
