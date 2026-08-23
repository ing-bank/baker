package com.ing.baker.recipe.wirespec;

import community.flock.wirespec.compiler.core.emit.LanguageEmitter;
import community.flock.wirespec.compiler.core.emit.FileExtension;
import community.flock.wirespec.compiler.core.emit.Shared;
import community.flock.wirespec.compiler.core.parse.ast.Channel;
import community.flock.wirespec.compiler.core.parse.ast.Endpoint;
import community.flock.wirespec.compiler.core.parse.ast.Enum;
import community.flock.wirespec.compiler.core.parse.ast.Field;
import community.flock.wirespec.compiler.core.parse.ast.Identifier;
import community.flock.wirespec.compiler.core.parse.ast.Module;
import community.flock.wirespec.compiler.core.parse.ast.Reference;
import community.flock.wirespec.compiler.core.parse.ast.Refined;
import community.flock.wirespec.compiler.core.parse.ast.Type;
import community.flock.wirespec.compiler.core.parse.ast.Union;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class BakerJavaEmitter extends LanguageEmitter {

    @NotNull
    @Override
    public String getSingleLineComment() {
        return "//";
    }

    @NotNull
    @Override
    public FileExtension getExtension() {
        return FileExtension.Java;
    }

    @Nullable
    @Override
    public Shared getShared() {
        return null;
    }

    @NotNull
    @Override
    public String notYetImplemented() {
        return "";
    }

    @NotNull
    @Override
    public String emit(@NotNull Identifier identifier) {
        return identifier.getValue();
    }

    @NotNull
    @Override
    public String emit(@NotNull Endpoint endpoint) {
        String name = emit(endpoint.getIdentifier());
        String interactionName = name + "Interaction";
        String outcomeName = name + "Outcome";

        StringBuilder sb = new StringBuilder();

        // Imports
        sb.append("import com.ing.baker.recipe.javadsl.Interaction;\n");
        sb.append("import com.ing.baker.recipe.annotations.FiresEvent;\n\n");

        // Interface
        sb.append("public interface ").append(interactionName).append(" extends Interaction {\n");
        sb.append("    interface ").append(outcomeName).append(" {}\n");

        // Response events — one per status code
        for (Endpoint.Response response : endpoint.getResponses()) {
            String eventName = name + "Response" + response.getStatus();
            if (response.getContent() != null) {
                String bodyType = emitReference(response.getContent().getReference());
                sb.append("    class ").append(eventName)
                  .append(" implements ").append(outcomeName).append(" {\n");
                sb.append("        public final ").append(bodyType).append(" body;\n");
                sb.append("        public ").append(eventName).append("(").append(bodyType).append(" body) { this.body = body; }\n");
                sb.append("    }\n");
            } else {
                sb.append("    class ").append(eventName)
                  .append(" implements ").append(outcomeName).append(" {}\n");
            }
        }

        sb.append("\n");

        // @FiresEvent annotation
        String responseClasses = endpoint.getResponses().stream()
            .map(r -> name + "Response" + r.getStatus() + ".class")
            .collect(Collectors.joining(", "));
        sb.append("    @FiresEvent(oneOf = {").append(responseClasses).append("})\n");

        // apply() method — collect all input params
        List<String[]> params = collectParams(endpoint);
        String paramList = params.stream()
            .map(p -> p[1] + " " + p[0])
            .collect(Collectors.joining(", "));
        sb.append("    ").append(outcomeName).append(" apply(").append(paramList).append(");\n");
        sb.append("}\n");

        return sb.toString();
    }

    @NotNull
    @Override
    public String emit(@NotNull Type type, @NotNull Module module) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Type.Shape shape) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Field field) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Reference reference) {
        return emitReference(reference);
    }

    @NotNull
    @Override
    public String emit(@NotNull Reference.Primitive.Type.Constraint constraint) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Enum anEnum, @NotNull Module module) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Union union) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Refined refined) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emitValidator(@NotNull Refined refined) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Channel channel) {
        return notYetImplemented();
    }

    /**
     * Maps wirespec Reference types to Java type names.
     */
    private String emitReference(Reference reference) {
        String typeName;
        if (reference instanceof Reference.Primitive primitive) {
            typeName = switch (primitive.getType()) {
                case Reference.Primitive.Type.String s -> "String";
                case Reference.Primitive.Type.Integer i -> switch (i.getPrecision()) {
                    case P32 -> "Integer";
                    case P64 -> "Long";
                };
                case Reference.Primitive.Type.Number n -> switch (n.getPrecision()) {
                    case P32 -> "Float";
                    case P64 -> "Double";
                };
                case Reference.Primitive.Type.Boolean b -> "Boolean";
                case Reference.Primitive.Type.Bytes b -> "byte[]";
                default -> "Object";
            };
        } else if (reference instanceof Reference.Custom custom) {
            typeName = custom.getValue();
        } else if (reference instanceof Reference.Iterable iterable) {
            typeName = "java.util.List<" + emitReference(iterable.getReference()) + ">";
        } else if (reference instanceof Reference.Dict dict) {
            typeName = "java.util.Map<String, " + emitReference(dict.getReference()) + ">";
        } else if (reference instanceof Reference.Unit u) {
            typeName = "Void";
        } else {
            typeName = "Object";
        }
        return typeName;
    }

    /**
     * Collects all input parameters from path segments, query params, headers, and request body.
     * Returns list of [name, type] pairs.
     */
    private List<String[]> collectParams(Endpoint endpoint) {
        List<String[]> params = new ArrayList<>();

        // Path parameters
        for (Endpoint.Segment segment : endpoint.getPath()) {
            if (segment instanceof Endpoint.Segment.Param param) {
                params.add(new String[]{
                    param.getIdentifier().getValue(),
                    emitReference(param.getReference())
                });
            }
        }

        // Query parameters
        for (Field query : endpoint.getQueries()) {
            params.add(new String[]{
                query.getIdentifier().getValue(),
                emitReference(query.getReference())
            });
        }

        // Header parameters
        for (Field header : endpoint.getHeaders()) {
            params.add(new String[]{
                header.getIdentifier().getValue(),
                emitReference(header.getReference())
            });
        }

        // Request body
        for (Endpoint.Request request : endpoint.getRequests()) {
            if (request.getContent() != null) {
                params.add(new String[]{
                    "body",
                    emitReference(request.getContent().getReference())
                });
            }
        }

        return params;
    }
}
