"""The public path boundary shared by packaging and content link validation."""

import json
from pathlib import Path, PurePosixPath

POLICY = json.loads(
    (Path(__file__).resolve().parents[1] / "infra/aws/public-files.json").read_text()
)


def is_safe_path(name):
    path = PurePosixPath(name)
    return (
        bool(path.parts)
        and not path.is_absolute()
        and all(
            part and not part.startswith(".") and "\\" not in part and "\0" not in part
            for part in path.parts
        )
    )


def is_public(name):
    path = PurePosixPath(name)
    return (
        is_safe_path(name)
        and (str(path) in POLICY["files"] or path.parts[0] in POLICY["roots"])
        and path.suffix.lower() in POLICY["extensions"]
    )


def checked_file(root, name):
    path = root / name
    for part in [path, *path.parents]:
        if part == root:
            break
        if part.is_symlink():
            raise ValueError(f"Public symlink refused: {part}")
    if not path.resolve().is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f"Missing or unsafe public file: {name}")
    return path


def selected_meshes(site):
    """Only saved manifests selected by the UI and their binary streams are deployed."""
    selected = set()
    records = json.loads(checked_file(site, "assets/atlas/index.json").read_text())["records"]
    renders = [
        json.loads(checked_file(site, record['path']).read_text())["render"]
        for record in records
    ]
    renders.append(json.loads(checked_file(site, "assets/home-scene.json").read_text()))
    for render in renders:
        if "mesh" not in render:
            continue  # generated in the browser
        name = PurePosixPath("assets") / render["mesh"]
        if name.parts[:2] != ("assets", "meshes") or not is_public(str(name)):
            raise ValueError(f"Unsafe mesh path: {name}")
        path = checked_file(site, name)
        selected.add(name.as_posix())
        manifest = json.loads(path.read_text())
        for key in ["vertices", "position", "normal", "complex", "indices"]:
            if key not in manifest:
                continue
            stream = name.parent / manifest[key]
            if not is_public(str(stream)) or stream.parent != name.parent:
                raise ValueError(f"Unsafe mesh stream: {stream}")
            checked_file(site, stream)
            selected.add(stream.as_posix())
    return selected
