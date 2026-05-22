package com.ing.baker.openapi.emitter;

import community.flock.wirespec.compiler.core.emit.Emitted;
import community.flock.wirespec.compiler.core.emit.FileExtension;
import community.flock.wirespec.compiler.core.emit.LanguageEmitter;
import community.flock.wirespec.compiler.core.emit.PackageName;
import community.flock.wirespec.compiler.core.emit.Shared;
import community.flock.wirespec.compiler.core.parse.ast.Channel;
import community.flock.wirespec.compiler.core.parse.ast.Definition;
import community.flock.wirespec.compiler.core.parse.ast.Endpoint;
import community.flock.wirespec.compiler.core.parse.ast.Enum;
import community.flock.wirespec.compiler.core.parse.ast.Field;
import community.flock.wirespec.compiler.core.parse.ast.Identifier;
import community.flock.wirespec.compiler.core.parse.ast.Module;
import community.flock.wirespec.compiler.core.parse.ast.Reference;
import community.flock.wirespec.compiler.core.parse.ast.Refined;
import community.flock.wirespec.compiler.core.parse.ast.Type;
import community.flock.wirespec.compiler.core.parse.ast.Union;
import community.flock.wirespec.compiler.utils.Logger;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class BakerOpenApiEmitter extends LanguageEmitter {

    private final PackageName packageName;
    private Module currentModule;

    public BakerOpenApiEmitter(PackageName packageName) {
        this.packageName = packageName;
    }

    public BakerOpenApiEmitter() {
        this.packageName = null;
    }

    @NotNull @Override public String getSingleLineComment() { return "//"; }
    @NotNull @Override public FileExtension getExtension() { return FileExtension.Kotlin; }
    @Nullable @Override public Shared getShared() { return null; }
    @NotNull @Override public String notYetImplemented() { return ""; }

    @NotNull
    @Override
    public Emitted emit(@NotNull Definition definition, @NotNull Module module, @NotNull Logger logger) {
        this.currentModule = module;
        Emitted base = super.emit(definition, module, logger);
        if (packageName != null && !packageName.getValue().isEmpty() && definition instanceof Endpoint) {
            String dir = packageName.getValue().replace('.', '/') + "/api/";
            return new Emitted(dir + base.getFile(), base.getResult());
        }
        return base;
    }

    @NotNull @Override public String emit(@NotNull Identifier identifier) { return identifier.getValue(); }

    @NotNull
    @Override
    public String emit(@NotNull Endpoint endpoint) {
        String name = emit(endpoint.getIdentifier());

        StringBuilder sb = new StringBuilder();
        if (packageName != null && !packageName.getValue().isEmpty()) {
            sb.append("package ").append(packageName.getValue()).append(".api\n\n");
            sb.append("import ").append(packageName.getValue()).append(".endpoint.").append(name).append("\n");
            sb.append("import ").append(packageName.getValue()).append(".model.*\n");
        }
        sb.append("import com.ing.baker.openapi.dsl.ApiOperation\n");
        sb.append("import com.ing.baker.openapi.dsl.InputField\n");
        sb.append("import community.flock.wirespec.kotlin.Wirespec\n");
        sb.append("import kotlin.reflect.KClass\n\n");

        sb.append("object ").append(name).append(" : ApiOperation {\n");
        sb.append("    override val operationName = \"").append(name).append("\"\n\n");

        // Input fields: path + query + headers + flattened body fields.
        // For ::class references we strip nullability — KClass has no nullable variant.
        List<String[]> inputs = collectInputs(endpoint);
        sb.append("    override val inputFields = listOf(\n");
        for (String[] f : inputs) {
            String classRef = f[1].endsWith("?") ? f[1].substring(0, f[1].length() - 1) : f[1];
            sb.append("        InputField(\"").append(f[0]).append("\", ").append(classRef).append("::class),\n");
        }
        sb.append("    )\n\n");

        // Response types
        sb.append("    override val responseTypes: Map<Int, KClass<*>> = mapOf(\n");
        for (Endpoint.Response resp : endpoint.getResponses()) {
            sb.append("        ").append(resp.getStatus()).append(" to ").append(name)
              .append(".Response").append(resp.getStatus()).append("::class,\n");
        }
        sb.append("    )\n\n");

        // handlerClass
        sb.append("    override val handlerClass = ").append(name).append(".Handler::class\n\n");

        // buildRequest
        String bodyTypeName = bodyTypeName(endpoint);
        List<String> ctorArgs = new ArrayList<>();
        for (Endpoint.Segment seg : endpoint.getPath()) {
            if (seg instanceof Endpoint.Segment.Param p) {
                ctorArgs.add(p.getIdentifier().getValue() + " = ingredients[\"" + p.getIdentifier().getValue() + "\"] as " + kotlinType(p.getReference()));
            }
        }
        for (Field q : endpoint.getQueries()) {
            ctorArgs.add(q.getIdentifier().getValue() + " = ingredients[\"" + q.getIdentifier().getValue() + "\"] as " + kotlinType(q.getReference()));
        }
        for (Field h : endpoint.getHeaders()) {
            ctorArgs.add(h.getIdentifier().getValue() + " = ingredients[\"" + h.getIdentifier().getValue() + "\"] as " + kotlinType(h.getReference()));
        }
        if (bodyTypeName != null) {
            Type bodyType = findType(bodyTypeName);
            StringBuilder bodyCtor = new StringBuilder(bodyTypeName + "(");
            if (bodyType != null) {
                String fields = bodyType.getShape().getValue().stream()
                    .map(f -> f.getIdentifier().getValue() + " = ingredients[\"" + f.getIdentifier().getValue() + "\"] as " + kotlinType(f.getReference()))
                    .collect(Collectors.joining(", "));
                bodyCtor.append(fields);
            }
            bodyCtor.append(")");
            ctorArgs.add(bodyCtor.toString());
        }
        sb.append("    override fun buildRequest(ingredients: Map<String, Any?>): Any =\n");
        sb.append("        ").append(name).append(".Request(\n");
        sb.append("            ").append(String.join(",\n            ", ctorArgs)).append("\n");
        sb.append("        )\n\n");

        // buildRequestFromBody — used by the typed inputFrom<E, R>(mapper) DSL.
        // The user-provided lambda returns the body DTO; this wraps it in the
        // Endpoint.Request envelope. Body-only operations have a trivial wrapper;
        // operations with path/query/header params reject the typed flow in v1.
        boolean bodyOnly = bodyTypeName != null
            && endpoint.getQueries().isEmpty()
            && endpoint.getHeaders().isEmpty()
            && endpoint.getPath().stream().noneMatch(s -> s instanceof Endpoint.Segment.Param);
        sb.append("    override fun buildRequestFromBody(body: Any): Any =\n");
        if (bodyOnly) {
            sb.append("        ").append(name).append(".Request(body as ").append(bodyTypeName).append(")\n\n");
        } else {
            sb.append("        error(\"inputFrom<E, R>(mapper) is not supported for operations with path/query/header params; use ingredientNameOverrides with the flat flow instead.\")\n\n");
        }

        // invoke
        String handlerMethod = Character.toLowerCase(name.charAt(0)) + name.substring(1);
        sb.append("    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> =\n");
        sb.append("        (handler as ").append(name).append(".Handler).").append(handlerMethod)
          .append("(request as ").append(name).append(".Request)\n\n");

        // buildHandler — wraps the operation's wirespec ClientEdge in a Handler that
        // routes through the supplied transport. Lets callers register no per-operation
        // factories — only (transport, serialization) at startup.
        sb.append("    override fun buildHandler(\n");
        sb.append("        transport: suspend (Wirespec.RawRequest) -> Wirespec.RawResponse,\n");
        sb.append("        serialization: Wirespec.Serialization,\n");
        sb.append("    ): Wirespec.Handler {\n");
        sb.append("        val edge = ").append(name).append(".Handler.client(serialization)\n");
        sb.append("        return object : ").append(name).append(".Handler {\n");
        sb.append("            override suspend fun ").append(handlerMethod)
          .append("(request: ").append(name).append(".Request): ")
          .append(name).append(".Response<*> =\n");
        sb.append("                edge.from(transport(edge.to(request)))\n");
        sb.append("        }\n");
        sb.append("    }\n");
        sb.append("}\n");

        return sb.toString();
    }

    @NotNull @Override public String emit(@NotNull Type type, @NotNull Module module) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Type.Shape shape) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Field field) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Reference reference) { return kotlinType(reference); }
    @NotNull @Override public String emit(@NotNull Reference.Primitive.Type.Constraint constraint) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Enum anEnum, @NotNull Module module) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Union union) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Refined refined) { return notYetImplemented(); }
    @NotNull @Override public String emitValidator(@NotNull Refined refined) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Channel channel) { return notYetImplemented(); }

    private List<String[]> collectInputs(Endpoint endpoint) {
        List<String[]> out = new ArrayList<>();
        for (Endpoint.Segment seg : endpoint.getPath()) {
            if (seg instanceof Endpoint.Segment.Param p) {
                out.add(new String[]{p.getIdentifier().getValue(), kotlinType(p.getReference())});
            }
        }
        for (Field q : endpoint.getQueries()) {
            out.add(new String[]{q.getIdentifier().getValue(), kotlinType(q.getReference())});
        }
        for (Field h : endpoint.getHeaders()) {
            out.add(new String[]{h.getIdentifier().getValue(), kotlinType(h.getReference())});
        }
        for (Endpoint.Request req : endpoint.getRequests()) {
            if (req.getContent() != null && req.getContent().getReference() instanceof Reference.Custom c) {
                Type bodyType = findType(c.getValue());
                if (bodyType != null) {
                    for (Field f : bodyType.getShape().getValue()) {
                        out.add(new String[]{f.getIdentifier().getValue(), kotlinType(f.getReference())});
                    }
                }
            }
        }
        return out;
    }

    private String bodyTypeName(Endpoint endpoint) {
        for (Endpoint.Request req : endpoint.getRequests()) {
            if (req.getContent() != null && req.getContent().getReference() instanceof Reference.Custom c) {
                return c.getValue();
            }
        }
        return null;
    }

    private Type findType(String name) {
        if (currentModule == null) return null;
        for (var stmt : currentModule.getStatements()) {
            if (stmt instanceof Type t && t.getIdentifier().getValue().equals(name)) return t;
        }
        return null;
    }

    private String kotlinType(Reference ref) {
        String base;
        if (ref instanceof Reference.Primitive primitive) {
            base = switch (primitive.getType()) {
                case Reference.Primitive.Type.String s -> "String";
                case Reference.Primitive.Type.Integer i -> switch (i.getPrecision()) {
                    case P32 -> "Int";
                    case P64 -> "Long";
                };
                case Reference.Primitive.Type.Number n -> switch (n.getPrecision()) {
                    case P32 -> "Float";
                    case P64 -> "Double";
                };
                case Reference.Primitive.Type.Boolean b -> "Boolean";
                case Reference.Primitive.Type.Bytes b -> "ByteArray";
                default -> "Any";
            };
        } else if (ref instanceof Reference.Custom c) {
            base = c.getValue();
        } else if (ref instanceof Reference.Iterable it) {
            base = "List<" + kotlinType(it.getReference()) + ">";
        } else if (ref instanceof Reference.Dict d) {
            base = "Map<String, " + kotlinType(d.getReference()) + ">";
        } else if (ref instanceof Reference.Unit) {
            base = "Unit";
        } else {
            base = "Any";
        }
        return ref.isNullable() ? base + "?" : base;
    }
}
