package com.ing.baker.recipe.wirespec;

import community.flock.wirespec.compiler.core.emit.Emitted;
import community.flock.wirespec.compiler.core.emit.LanguageEmitter;
import community.flock.wirespec.compiler.core.emit.FileExtension;
import community.flock.wirespec.compiler.core.emit.PackageName;
import community.flock.wirespec.compiler.core.emit.Shared;
import community.flock.wirespec.compiler.core.parse.ast.Definition;
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
import community.flock.wirespec.compiler.utils.Logger;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class BakerKotlinEmitter extends LanguageEmitter {

    private final PackageName packageName;
    private Module currentModule;

    public BakerKotlinEmitter(PackageName packageName) {
        this.packageName = packageName;
    }

    public BakerKotlinEmitter() {
        this.packageName = null;
    }

    /**
     * Sets the module context for type lookups during flattening.
     * Package-private for testing purposes.
     */
    void setModule(Module module) {
        this.currentModule = module;
    }

    @NotNull
    @Override
    public String getSingleLineComment() {
        return "//";
    }

    @NotNull
    @Override
    public FileExtension getExtension() {
        return FileExtension.Kotlin;
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
    public Emitted emit(@NotNull Definition definition, @NotNull Module module, @NotNull Logger logger) {
        this.currentModule = module;
        Emitted base = super.emit(definition, module, logger);
        if (packageName != null && !packageName.getValue().isEmpty()) {
            String dir = packageName.getValue().replace('.', '/') + "/interaction/";
            return new Emitted(dir + base.getFile(), base.getResult());
        }
        return base;
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

        // Package declaration
        if (packageName != null && !packageName.getValue().isEmpty()) {
            sb.append("package ").append(packageName.getValue()).append(".interaction").append("\n\n");
        }

        // Collect referenced custom types for imports
        Set<String> customTypes = collectCustomTypeNames(endpoint);

        // Import Baker Interaction and coroutines
        sb.append("import com.ing.baker.recipe.javadsl.Interaction\n");
        sb.append("import kotlinx.coroutines.runBlocking\n");

        // Import referenced types from endpoint and model sub-packages
        if (packageName != null && !packageName.getValue().isEmpty()) {
            String pkg = packageName.getValue();
            // Import endpoint class (for Handler, Request, Response types)
            sb.append("import ").append(pkg).append(".endpoint.").append(name).append("\n");
            // Import model types
            for (String typeName : customTypes) {
                sb.append("import ").append(pkg).append(".model.").append(typeName).append("\n");
            }
        }

        sb.append("\n");

        // Interface
        sb.append("interface ").append(interactionName).append(" : Interaction {\n");
        sb.append("    sealed interface ").append(outcomeName).append("\n");

        // Response events — one per status code
        for (Endpoint.Response response : endpoint.getResponses()) {
            String eventName = name + "Response" + response.getStatus();
            if (response.getContent() != null) {
                Reference ref = response.getContent().getReference();
                if (ref instanceof Reference.Custom custom) {
                    Type responseType = findTypeInModule(custom.getValue());
                    if (responseType != null) {
                        // Flatten response fields
                        String fields = responseType.getShape().getValue().stream()
                            .map(f -> "val " + f.getIdentifier().getValue() + ": " + emitReference(f.getReference()))
                            .collect(Collectors.joining(", "));
                        sb.append("    data class ").append(eventName)
                          .append("(").append(fields).append(") : ")
                          .append(outcomeName).append("\n");
                    } else {
                        // Fallback: use body param
                        sb.append("    data class ").append(eventName)
                          .append("(val body: ").append(custom.getValue()).append(") : ")
                          .append(outcomeName).append("\n");
                    }
                } else {
                    String bodyType = emitReference(ref);
                    sb.append("    data class ").append(eventName)
                      .append("(val body: ").append(bodyType).append(") : ")
                      .append(outcomeName).append("\n");
                }
            } else {
                sb.append("    data object ").append(eventName).append(" : ")
                  .append(outcomeName).append("\n");
            }
        }

        sb.append("\n");

        // apply() method — collect all input params
        List<String[]> params = collectParams(endpoint);
        String paramList = params.stream()
            .map(p -> p[0] + ": " + p[1])
            .collect(Collectors.joining(", "));
        sb.append("    fun apply(").append(paramList).append("): ").append(outcomeName).append("\n");
        sb.append("}\n\n");

        // Find request body type info for implementation
        String requestBodyTypeName = null;
        Type requestBodyType = null;
        for (Endpoint.Request request : endpoint.getRequests()) {
            if (request.getContent() != null && request.getContent().getReference() instanceof Reference.Custom custom) {
                requestBodyTypeName = custom.getValue();
                requestBodyType = findTypeInModule(custom.getValue());
                break;
            }
        }

        // Implementation class
        String handlerMethod = Character.toLowerCase(name.charAt(0)) + name.substring(1);
        sb.append("class ").append(interactionName).append("Impl(\n");
        sb.append("    private val client: ").append(name).append(".Handler\n");
        sb.append(") : ").append(interactionName).append(" {\n");

        sb.append("    override fun apply(").append(paramList).append("): ")
          .append(interactionName).append(".").append(outcomeName).append(" {\n");

        if (requestBodyType != null) {
            // Construct body from flattened params
            String namedArgs = requestBodyType.getShape().getValue().stream()
                .map(f -> f.getIdentifier().getValue() + " = " + f.getIdentifier().getValue())
                .collect(Collectors.joining(", "));
            sb.append("        val body = ").append(requestBodyTypeName).append("(").append(namedArgs).append(")\n");
            // Build request with non-body params + body
            List<String> requestArgs = new ArrayList<>();
            // Path params
            for (Endpoint.Segment segment : endpoint.getPath()) {
                if (segment instanceof Endpoint.Segment.Param param) {
                    requestArgs.add(param.getIdentifier().getValue());
                }
            }
            // Query params
            for (Field query : endpoint.getQueries()) {
                requestArgs.add(query.getIdentifier().getValue());
            }
            // Header params
            for (Field header : endpoint.getHeaders()) {
                requestArgs.add(header.getIdentifier().getValue());
            }
            // Body
            requestArgs.add("body");
            String requestArgList = String.join(", ", requestArgs);
            sb.append("        val request = ").append(name).append(".Request(").append(requestArgList).append(")\n");
        } else {
            String argList = params.stream()
                .map(p -> p[0])
                .collect(Collectors.joining(", "));
            sb.append("        val request = ").append(name).append(".Request(").append(argList).append(")\n");
        }

        sb.append("        val response = runBlocking { client.").append(handlerMethod).append("(request) }\n");
        sb.append("        return when (response) {\n");

        for (Endpoint.Response response : endpoint.getResponses()) {
            String eventName = name + "Response" + response.getStatus();
            sb.append("            is ").append(name).append(".Response").append(response.getStatus())
              .append(" -> ").append(interactionName).append(".").append(eventName);
            if (response.getContent() != null) {
                Reference ref = response.getContent().getReference();
                if (ref instanceof Reference.Custom custom) {
                    Type responseType = findTypeInModule(custom.getValue());
                    if (responseType != null) {
                        String fieldMappings = responseType.getShape().getValue().stream()
                            .map(f -> f.getIdentifier().getValue() + " = response.body." + f.getIdentifier().getValue())
                            .collect(Collectors.joining(", "));
                        sb.append("(").append(fieldMappings).append(")");
                    } else {
                        sb.append("(response.body)");
                    }
                } else {
                    sb.append("(response.body)");
                }
            }
            sb.append("\n");
        }

        sb.append("        }\n");
        sb.append("    }\n");
        sb.append("}");

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
     * Looks up a Type definition by name in the current module.
     */
    private Type findTypeInModule(String typeName) {
        if (currentModule == null) return null;
        for (var stmt : currentModule.getStatements()) {
            if (stmt instanceof Type type && type.getIdentifier().getValue().equals(typeName)) {
                return type;
            }
        }
        return null;
    }

    /**
     * Maps wirespec Reference types to Kotlin type names.
     */
    private String emitReference(Reference reference) {
        String typeName;
        if (reference instanceof Reference.Primitive primitive) {
            typeName = switch (primitive.getType()) {
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
        } else if (reference instanceof Reference.Custom custom) {
            typeName = custom.getValue();
        } else if (reference instanceof Reference.Iterable iterable) {
            typeName = "List<" + emitReference(iterable.getReference()) + ">";
        } else if (reference instanceof Reference.Dict dict) {
            typeName = "Map<String, " + emitReference(dict.getReference()) + ">";
        } else if (reference instanceof Reference.Unit u) {
            typeName = "Unit";
        } else {
            typeName = "Any";
        }
        return reference.isNullable() ? typeName + "?" : typeName;
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

        // Request body — flatten if possible
        for (Endpoint.Request request : endpoint.getRequests()) {
            if (request.getContent() != null) {
                Reference ref = request.getContent().getReference();
                if (ref instanceof Reference.Custom custom) {
                    Type bodyType = findTypeInModule(custom.getValue());
                    if (bodyType != null) {
                        // Flatten: add each field as a parameter
                        for (Field field : bodyType.getShape().getValue()) {
                            params.add(new String[]{
                                field.getIdentifier().getValue(),
                                emitReference(field.getReference())
                            });
                        }
                        continue; // skip adding "body" param
                    }
                }
                // Fallback: add as "body" param
                params.add(new String[]{
                    "body",
                    emitReference(ref)
                });
            }
        }

        return params;
    }

    /**
     * Collects all custom (non-primitive) type names referenced in an endpoint.
     * When flattening is possible, also collects the body type itself and any custom types in its fields.
     */
    private Set<String> collectCustomTypeNames(Endpoint endpoint) {
        Set<String> types = new HashSet<>();

        // Request body types
        for (Endpoint.Request request : endpoint.getRequests()) {
            if (request.getContent() != null) {
                Reference ref = request.getContent().getReference();
                collectCustomTypeNamesFromRef(ref, types);
                // When flattening, also collect custom types from the body type's fields
                if (ref instanceof Reference.Custom custom) {
                    Type bodyType = findTypeInModule(custom.getValue());
                    if (bodyType != null) {
                        for (Field field : bodyType.getShape().getValue()) {
                            collectCustomTypeNamesFromRef(field.getReference(), types);
                        }
                    }
                }
            }
        }

        // Response body types
        for (Endpoint.Response response : endpoint.getResponses()) {
            if (response.getContent() != null) {
                Reference ref = response.getContent().getReference();
                collectCustomTypeNamesFromRef(ref, types);
                // When flattening, also collect custom types from the response type's fields
                if (ref instanceof Reference.Custom custom) {
                    Type responseType = findTypeInModule(custom.getValue());
                    if (responseType != null) {
                        for (Field field : responseType.getShape().getValue()) {
                            collectCustomTypeNamesFromRef(field.getReference(), types);
                        }
                    }
                }
            }
        }

        return types;
    }

    private void collectCustomTypeNamesFromRef(Reference reference, Set<String> types) {
        if (reference instanceof Reference.Custom custom) {
            types.add(custom.getValue());
        } else if (reference instanceof Reference.Iterable iterable) {
            collectCustomTypeNamesFromRef(iterable.getReference(), types);
        } else if (reference instanceof Reference.Dict dict) {
            collectCustomTypeNamesFromRef(dict.getReference(), types);
        }
    }
}
