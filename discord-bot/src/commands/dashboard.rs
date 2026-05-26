//! `/dregg` Starbridge dashboard and rich Discord component flows.

use serenity::all::{
    ActionRowComponent, ButtonStyle, CommandInteraction, ComponentInteraction,
    ComponentInteractionDataKind, Context, CreateActionRow, CreateButton, CreateCommand,
    CreateEmbed, CreateInputText, CreateInteractionResponse, CreateInteractionResponseMessage,
    CreateModal, CreateSelectMenu, CreateSelectMenuKind, CreateSelectMenuOption, InputTextStyle,
    ModalInteraction,
};

use dregg_app_framework::{CellId, FieldElement, field_from_bytes, hex_encode_32};
use dregg_dfa::{RouteTable, RouteTarget};
use starbridge_nameservice::{build_register_action, build_set_target_action};
use starbridge_governed_namespace::{
    VoteKind, build_propose_table_update_action, build_route_table, build_vote_on_proposal_action,
    route_table_commitment,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::credential_issue;
use crate::db::IdentityMode;
use crate::embeds;

const ID_HOME: &str = "dregg:home";
const ID_APP_SELECT: &str = "dregg:app_select";
const ID_APP_IDENTITY: &str = "dregg:app:identity";
const ID_APP_NAMES: &str = "dregg:app:names";
const ID_APP_GOV: &str = "dregg:app:governance";
const ID_APP_SUBS: &str = "dregg:app:subscription";

const ID_NAME_REGISTER: &str = "dregg:modal:name_register";
const ID_NAME_RESOLVE: &str = "dregg:modal:name_resolve";
const ID_CRED_ISSUE: &str = "dregg:modal:credential_issue";
const ID_CRED_VERIFY: &str = "dregg:modal:credential_verify";
const ID_GOV_PROPOSE: &str = "dregg:modal:gov_propose";
const ID_GOV_VOTE: &str = "dregg:modal:gov_vote";
const ID_SUB_CREATE: &str = "dregg:modal:sub_create";
const ID_SUB_PUBLISH: &str = "dregg:modal:sub_publish";
const ID_SUB_SUBSCRIBE: &str = "dregg:modal:sub_subscribe";

pub fn register() -> CreateCommand {
    CreateCommand::new("dregg").description("Open your Starbridge app dashboard")
}

pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let embed = home_embed(command.user.id.get(), state).await;
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(home_components())
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.as_str();

    if id == ID_APP_SELECT {
        if let ComponentInteractionDataKind::StringSelect { values } = &component.data.kind {
            if let Some(value) = values.first() {
                update_panel(ctx, component, state, value).await;
                return;
            }
        }
    }

    match id {
        ID_HOME => {
            let embed = home_embed(component.user.id.get(), state).await;
            update_message(ctx, component, embed, home_components()).await;
        }
        ID_APP_IDENTITY => update_panel(ctx, component, state, "identity").await,
        ID_APP_NAMES => update_panel(ctx, component, state, "names").await,
        ID_APP_GOV => update_panel(ctx, component, state, "governance").await,
        ID_APP_SUBS => update_panel(ctx, component, state, "subscription").await,
        ID_NAME_REGISTER => {
            open_modal(ctx, component, name_register_modal()).await;
        }
        ID_NAME_RESOLVE => {
            open_modal(ctx, component, name_resolve_modal()).await;
        }
        ID_CRED_ISSUE => {
            open_modal(ctx, component, credential_issue_modal()).await;
        }
        ID_CRED_VERIFY => {
            open_modal(ctx, component, credential_verify_modal()).await;
        }
        ID_GOV_PROPOSE => {
            open_modal(ctx, component, gov_propose_modal()).await;
        }
        ID_GOV_VOTE => {
            open_modal(ctx, component, gov_vote_modal()).await;
        }
        ID_SUB_CREATE => {
            open_modal(ctx, component, subscription_create_modal()).await;
        }
        ID_SUB_PUBLISH => {
            open_modal(ctx, component, subscription_publish_modal()).await;
        }
        ID_SUB_SUBSCRIBE => {
            open_modal(ctx, component, subscription_subscribe_modal()).await;
        }
        _ => {
            let msg = CreateInteractionResponseMessage::new()
                .embed(embeds::warning_embed(
                    "Unknown Control",
                    "This dashboard control is not recognized by this bot build.",
                ))
                .ephemeral(true);
            let _ = component
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
    }
}

pub async fn handle_modal(ctx: &Context, modal: &ModalInteraction, state: &BotState) {
    let custom_id = modal.data.custom_id.as_str();
    let embed = match custom_id {
        ID_NAME_REGISTER => submit_name_register(modal, state).await,
        ID_NAME_RESOLVE => submit_name_resolve(modal, state).await,
        ID_CRED_ISSUE => submit_credential_issue(modal, state).await,
        ID_CRED_VERIFY => submit_credential_verify(modal, state).await,
        ID_GOV_PROPOSE => submit_gov_propose(modal, state).await,
        ID_GOV_VOTE => submit_gov_vote(modal, state).await,
        ID_SUB_CREATE => submit_subscription_create(modal, state).await,
        ID_SUB_PUBLISH => submit_subscription_publish(modal, state).await,
        ID_SUB_SUBSCRIBE => submit_subscription_subscribe(modal, state).await,
        _ => embeds::warning_embed(
            "Unknown Form",
            "This submitted form is not recognized by this bot build.",
        ),
    };

    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(home_components())
        .ephemeral(true);
    let _ = modal
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

async fn update_panel(
    ctx: &Context,
    component: &ComponentInteraction,
    state: &BotState,
    app: &str,
) {
    let (embed, components) = match app {
        "identity" => (
            identity_embed(component.user.id.get(), state).await,
            identity_components(),
        ),
        "names" => (
            names_embed(component.guild_id.map(|id| id.get())),
            names_components(),
        ),
        "governance" => (
            governance_embed(component.guild_id.map(|id| id.get())),
            governance_components(),
        ),
        "subscription" => (
            subscription_embed(component.guild_id.map(|id| id.get())),
            subscription_components(),
        ),
        _ => (
            embeds::warning_embed(
                "Unknown App",
                "Pick one of the Starbridge apps in the menu.",
            ),
            home_components(),
        ),
    };
    update_message(ctx, component, embed, components).await;
}

async fn update_message(
    ctx: &Context,
    component: &ComponentInteraction,
    embed: CreateEmbed,
    components: Vec<CreateActionRow>,
) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(components);
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::UpdateMessage(msg))
        .await;
}

async fn open_modal(ctx: &Context, component: &ComponentInteraction, modal: CreateModal) {
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Modal(modal))
        .await;
}

async fn home_embed(user_id: u64, state: &BotState) -> CreateEmbed {
    let identity = state
        .db
        .get_user_identity(&user_id.to_string())
        .await
        .ok()
        .flatten();
    let cell = identity
        .as_ref()
        .map(|i| format!("`{}...`", &i.cell_id[..16.min(i.cell_id.len())]))
        .unwrap_or_else(|| "not created".to_string());
    let mode = identity.as_ref().map(|i| i.mode.as_str()).unwrap_or("none");

    embeds::dregg_embed("Starbridge Apps")
        .description("Pick an app, then use the buttons to open focused Discord forms.")
        .field("Cell", cell, true)
        .field("Identity Mode", mode, true)
        .field(
            "RemoteRuntime",
            format!("`{}`", state.config.devnet_url),
            false,
        )
}

async fn identity_embed(user_id: u64, state: &BotState) -> CreateEmbed {
    let identity = state
        .db
        .get_user_identity(&user_id.to_string())
        .await
        .ok()
        .flatten();
    let cell = identity
        .as_ref()
        .map(|i| format!("`{}...`", &i.cell_id[..16.min(i.cell_id.len())]))
        .unwrap_or_else(|| "create `/cipherclerk create` first".to_string());

    embeds::dregg_embed("Identity")
        .description("Issue credentials and request selective-disclosure proofs.")
        .field("Issuer / Verifier Cell", cell, false)
        .field("Starbridge App", "`starbridge-apps/identity`", true)
}

fn names_embed(guild_id: Option<u64>) -> CreateEmbed {
    embeds::dregg_embed("Nameservice")
        .description("Register and resolve names in this Discord guild namespace.")
        .field(
            "Namespace",
            guild_id
                .map(|id| format!("`/discord/{id}/`"))
                .unwrap_or_else(|| "guild required".to_string()),
            false,
        )
        .field("Starbridge App", "`starbridge-apps/nameservice`", true)
}

fn governance_embed(guild_id: Option<u64>) -> CreateEmbed {
    embeds::dregg_embed("Governed Namespace")
        .description("Create proposal cards and cast votes for route-table or parameter changes.")
        .field(
            "Guild Federation",
            guild_id
                .map(|id| format!("`{id}`"))
                .unwrap_or_else(|| "guild required".to_string()),
            true,
        )
        .field(
            "Starbridge App",
            "`starbridge-apps/governed-namespace`",
            true,
        )
}

fn subscription_embed(guild_id: Option<u64>) -> CreateEmbed {
    embeds::dregg_embed("Subscription")
        .description("Create, publish to, and subscribe to Discord-mounted Starbridge queues.")
        .field(
            "Mount Prefix",
            guild_id
                .map(|id| format!("`/discord/{id}/<name>`"))
                .unwrap_or_else(|| "guild required".to_string()),
            false,
        )
        .field("Starbridge App", "`starbridge-apps/subscription`", true)
}

fn home_components() -> Vec<CreateActionRow> {
    vec![
        app_select(),
        CreateActionRow::Buttons(vec![
            button(ID_APP_IDENTITY, "Identity", ButtonStyle::Primary),
            button(ID_APP_NAMES, "Names", ButtonStyle::Primary),
            button(ID_APP_GOV, "Governance", ButtonStyle::Primary),
            button(ID_APP_SUBS, "Subscription", ButtonStyle::Primary),
        ]),
    ]
}

fn identity_components() -> Vec<CreateActionRow> {
    vec![
        app_select(),
        CreateActionRow::Buttons(vec![
            button(ID_CRED_ISSUE, "Issue Credential", ButtonStyle::Success),
            button(ID_CRED_VERIFY, "Request Proof", ButtonStyle::Primary),
            button(ID_HOME, "Home", ButtonStyle::Secondary),
        ]),
    ]
}

fn names_components() -> Vec<CreateActionRow> {
    vec![
        app_select(),
        CreateActionRow::Buttons(vec![
            button(ID_NAME_REGISTER, "Register Name", ButtonStyle::Success),
            button(ID_NAME_RESOLVE, "Resolve Name", ButtonStyle::Primary),
            button(ID_HOME, "Home", ButtonStyle::Secondary),
        ]),
    ]
}

fn governance_components() -> Vec<CreateActionRow> {
    vec![
        app_select(),
        CreateActionRow::Buttons(vec![
            button(ID_GOV_PROPOSE, "New Proposal", ButtonStyle::Success),
            button(ID_GOV_VOTE, "Vote", ButtonStyle::Primary),
            button(ID_HOME, "Home", ButtonStyle::Secondary),
        ]),
    ]
}

fn subscription_components() -> Vec<CreateActionRow> {
    vec![
        app_select(),
        CreateActionRow::Buttons(vec![
            button(ID_SUB_CREATE, "Create Queue", ButtonStyle::Success),
            button(ID_SUB_PUBLISH, "Publish", ButtonStyle::Primary),
            button(ID_SUB_SUBSCRIBE, "Subscribe", ButtonStyle::Primary),
            button(ID_HOME, "Home", ButtonStyle::Secondary),
        ]),
    ]
}

fn app_select() -> CreateActionRow {
    CreateActionRow::SelectMenu(
        CreateSelectMenu::new(
            ID_APP_SELECT,
            CreateSelectMenuKind::String {
                options: vec![
                    CreateSelectMenuOption::new("Identity", "identity")
                        .description("Credentials and selective disclosure"),
                    CreateSelectMenuOption::new("Nameservice", "names")
                        .description("Guild names, resolution, and ownership"),
                    CreateSelectMenuOption::new("Governed Namespace", "governance")
                        .description("Proposals, votes, and route-table governance"),
                    CreateSelectMenuOption::new("Subscription", "subscription")
                        .description("Pub/sub queues mounted into Discord"),
                ],
            },
        )
        .placeholder("Choose a Starbridge app")
        .min_values(1)
        .max_values(1),
    )
}

fn button(id: &str, label: &str, style: ButtonStyle) -> CreateButton {
    CreateButton::new(id).label(label).style(style)
}

fn name_register_modal() -> CreateModal {
    CreateModal::new(ID_NAME_REGISTER, "Register Name").components(vec![
        short_row(short_input("name", "Name", "alice").max_length(80)),
        short_row(short_input("registry_cell", "Registry cell id", "64 hex chars").max_length(64)),
        short_row(short_input("expiry_height", "Expiry height", "1000000").max_length(20)),
        short_row(
            short_input(
                "target",
                "Target cell or URI",
                "optional dregg:// or cell id",
            )
            .required(false)
            .max_length(256),
        ),
    ])
}

fn name_resolve_modal() -> CreateModal {
    CreateModal::new(ID_NAME_RESOLVE, "Resolve Name").components(vec![short_row(
        short_input("name", "Name", "alice").max_length(80),
    )])
}

fn credential_issue_modal() -> CreateModal {
    CreateModal::new(ID_CRED_ISSUE, "Issue Credential").components(vec![
        short_row(short_input("schema", "Schema", "kyc").max_length(80)),
        CreateActionRow::InputText(
            CreateInputText::new(InputTextStyle::Paragraph, "Attributes JSON", "attributes")
                .placeholder(r#"{"country":"US","age_over_18":true}"#)
                .max_length(2000),
        ),
    ])
}

fn credential_verify_modal() -> CreateModal {
    CreateModal::new(ID_CRED_VERIFY, "Request Credential Proof").components(vec![
        short_row(short_input("subject", "Subject cell id", "64 hex chars").max_length(128)),
        short_row(short_input("predicate", "Predicate", "age>=18").max_length(200)),
    ])
}

fn gov_propose_modal() -> CreateModal {
    CreateModal::new(ID_GOV_PROPOSE, "Create Governance Proposal").components(vec![
        short_row(short_input("namespace_cell", "Namespace cell id", "64 hex chars").max_length(64)),
        CreateActionRow::InputText(
            CreateInputText::new(InputTextStyle::Paragraph, "Routes JSON", "routes_json")
                .placeholder(r#"[{"path":"/public/*","target":"public"}]"#)
                .max_length(2000),
        ),
        short_row(
            short_input("dispute_window_height", "Dispute window height", "1000").max_length(20),
        ),
        CreateActionRow::InputText(
            CreateInputText::new(InputTextStyle::Paragraph, "Description", "description")
                .placeholder("Describe the route-table update")
                .max_length(2000),
        ),
    ])
}

fn gov_vote_modal() -> CreateModal {
    CreateModal::new(ID_GOV_VOTE, "Vote on Proposal").components(vec![
        short_row(short_input("namespace_cell", "Namespace cell id", "64 hex chars").max_length(64)),
        short_row(
            short_input("prior_proposal_root", "Prior proposal root", "64 hex chars")
                .max_length(64),
        ),
        short_row(short_input("vote", "Vote", "yes or no").max_length(8)),
    ])
}

fn subscription_create_modal() -> CreateModal {
    CreateModal::new(ID_SUB_CREATE, "Create Subscription Queue").components(vec![
        short_row(short_input("name", "Queue name", "announcements").max_length(80)),
        short_row(
            short_input("rate_limit", "Rate limit per minute", "optional number")
                .required(false)
                .max_length(8),
        ),
        short_row(
            short_input("deposit", "Minimum deposit", "optional computrons")
                .required(false)
                .max_length(16),
        ),
    ])
}

fn subscription_publish_modal() -> CreateModal {
    CreateModal::new(ID_SUB_PUBLISH, "Publish to Queue").components(vec![
        short_row(short_input("name", "Queue name", "announcements").max_length(80)),
        CreateActionRow::InputText(
            CreateInputText::new(InputTextStyle::Paragraph, "Message", "message")
                .placeholder("Message payload")
                .max_length(2000),
        ),
    ])
}

fn subscription_subscribe_modal() -> CreateModal {
    CreateModal::new(ID_SUB_SUBSCRIBE, "Subscribe to Queue").components(vec![short_row(
        short_input("name", "Queue name", "announcements").max_length(80),
    )])
}

fn short_input(id: &str, label: &str, placeholder: &str) -> CreateInputText {
    CreateInputText::new(InputTextStyle::Short, label, id)
        .placeholder(placeholder)
        .max_length(256)
}

fn short_row(input: CreateInputText) -> CreateActionRow {
    CreateActionRow::InputText(input)
}

async fn submit_name_register(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let name = modal_value(modal, "name");
    let registry_cell_hex = modal_value(modal, "registry_cell");
    let expiry_height = match modal_value(modal, "expiry_height").parse::<u64>() {
        Ok(value) => value,
        Err(_) => {
            return embeds::warning_embed(
                "Invalid Expiry",
                "Expiry height must be an unsigned integer.",
            );
        }
    };
    let target = modal_value(modal, "target");
    let owner = match user_cell(modal.user.id.get(), state).await {
        Ok(cell) => cell,
        Err(embed) => return embed,
    };
    if let Err(embed) = hosted_user_cell(modal.user.id.get(), state).await {
        return embed;
    }

    let registry_cell = match parse_cell_id(&registry_cell_hex) {
        Ok(cell) => cell,
        Err(embed) => return embed,
    };
    let owner_bytes = match parse_cell_bytes(&owner) {
        Ok(bytes) => bytes,
        Err(embed) => return embed,
    };

    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        modal.user.id.get(),
        state.federation_id_bytes,
    );
    let mut actions = vec![build_register_action(
        &cclerk.app,
        registry_cell,
        &name,
        owner_bytes,
        expiry_height,
    )];
    if !target.is_empty() {
        actions.push(build_set_target_action(
            &cclerk.app,
            registry_cell,
            &name,
            field_from_bytes(target.as_bytes()),
        ));
    }

    match state
        .devnet
        .submit_app_actions(
            &cclerk,
            actions,
            Some(format!("discord:nameservice:register:{name}")),
        )
        .await
    {
        Ok(result) if result.accepted => embeds::success_embed("Name Registered")
            .field("Name", name, true)
            .field("Owner", short_cell(&owner), true)
            .field("Registry", short_cell(&registry_cell_hex), true)
            .field(
                "Turn",
                result
                    .turn_hash
                    .map(|hash| format!("`{hash}`"))
                    .unwrap_or_else(|| "`unknown`".to_string()),
                false,
            ),
        Ok(result) => embeds::error_embed(
            "Registration Rejected",
            result
                .error
                .as_deref()
                .unwrap_or("node rejected the signed turn"),
        ),
        Err(e) => embeds::error_embed("Node Unreachable", &e.to_string()),
    }
}

async fn submit_name_resolve(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let Some(guild_id) = modal.guild_id.map(|id| id.get()) else {
        return embeds::warning_embed("Guild Required", "Names resolve inside a server namespace.");
    };
    let name = modal_value(modal, "name");
    match state
        .devnet
        .client()
        .get(format!("{}/names/resolve", state.config.devnet_url))
        .query(&[("guild_id", guild_id.to_string()), ("name", name.clone())])
        .send()
        .await
    {
        Ok(resp) if resp.status().is_success() => {
            let value: serde_json::Value = resp.json().await.unwrap_or_default();
            embeds::dregg_embed("Name Resolved")
                .field("Name", name, true)
                .field("Cell ID", code_field(value.get("cell_id")), false)
                .field("URI", code_block(value.get("uri")), false)
        }
        Ok(resp) if resp.status().as_u16() == 404 => embeds::warning_embed(
            "Name Not Found",
            &format!("No registration found for `{name}`."),
        ),
        Ok(resp) => embeds::error_embed("Resolve Failed", &response_text(resp).await),
        Err(e) => embeds::error_embed("Node Unreachable", &e.to_string()),
    }
}

async fn submit_credential_issue(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let schema = modal_value(modal, "schema");
    let attributes = modal_value(modal, "attributes");
    let user_id = modal.user.id.get();
    let cell = match hosted_user_cell(user_id, state).await {
        Ok(cell) => cell,
        Err(embed) => return embed,
    };

    match credential_issue::issue_from_discord_input(state, user_id, &cell, &schema, &attributes)
        .await
    {
        Ok(result) => embeds::success_embed("Credential Issued")
            .field("Schema", result.schema, true)
            .field("Credential ID", format!("`{}`", result.credential_id), true)
            .field(
                "Turn",
                result
                    .turn
                    .turn_hash
                    .map(|hash| format!("`{hash}`"))
                    .unwrap_or_else(|| "`unknown`".to_string()),
                false,
            ),
        Err(e) => embeds::error_embed("Issue Failed", &e.to_string()),
    }
}

async fn submit_credential_verify(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let subject = modal_value(modal, "subject");
    let predicate = modal_value(modal, "predicate");
    let verifier = match user_cell(modal.user.id.get(), state).await {
        Ok(cell) => cell,
        Err(embed) => return embed,
    };

    match state
        .devnet
        .request_proof(&verifier, &subject, &predicate)
        .await
    {
        Ok(result) => embeds::success_embed("Proof Requested")
            .field("Subject Cell", short_cell(&subject), true)
            .field("Predicate", predicate, true)
            .field("Request ID", format!("`{}`", result.request_id), true)
            .field("Status", result.status, true),
        Err(e) => embeds::error_embed("Verification Request Failed", &e.to_string()),
    }
}

async fn submit_gov_propose(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let Some(guild_id) = modal.guild_id.map(|id| id.get()) else {
        return embeds::warning_embed(
            "Guild Required",
            "Governance proposals must be made in a server.",
        );
    };
    let namespace_cell_hex = modal_value(modal, "namespace_cell");
    let routes_json = modal_value(modal, "routes_json");
    let dispute_window_height = match modal_value(modal, "dispute_window_height").parse::<u64>() {
        Ok(value) => value,
        Err(_) => {
            return embeds::warning_embed(
                "Invalid Dispute Window",
                "Dispute window height must be an unsigned integer.",
            );
        }
    };
    let description = modal_value(modal, "description");
    if let Err(embed) = hosted_user_cell(modal.user.id.get(), state).await {
        return embed;
    }
    let namespace_cell = match parse_cell_id(&namespace_cell_hex) {
        Ok(cell) => cell,
        Err(embed) => return embed,
    };
    let route_table = match parse_route_table(&routes_json) {
        Ok(table) => table,
        Err(embed) => return embed,
    };
    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        modal.user.id.get(),
        state.federation_id_bytes,
    );
    let proposed_root = route_table_commitment(&route_table);
    let action = build_propose_table_update_action(
        &cclerk.app,
        namespace_cell,
        &route_table,
        dispute_window_height,
        &description,
    );
    match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:governance:propose:guild:{guild_id}")),
        )
        .await
    {
        Ok(result) if result.accepted => embeds::success_embed("Proposal Submitted")
            .field("Namespace", short_cell(&namespace_cell_hex), true)
            .field("Proposed Root", format!("`{}`", hex_encode_32(&proposed_root)), false)
            .field("Dispute Window", dispute_window_height.to_string(), true)
            .field("Description", truncate(&description, 900), false)
            .field("Turn", turn_hash_field(result.turn_hash), false),
        Ok(result) => embeds::error_embed(
            "Proposal Rejected",
            result
                .error
                .as_deref()
                .unwrap_or("node rejected the signed governance action"),
        ),
        Err(e) => embeds::error_embed("Node Unreachable", &e.to_string()),
    }
}

async fn submit_gov_vote(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let Some(guild_id) = modal.guild_id.map(|id| id.get()) else {
        return embeds::warning_embed(
            "Guild Required",
            "Governance votes must be cast in a server.",
        );
    };
    let namespace_cell_hex = modal_value(modal, "namespace_cell");
    let prior_proposal_root_hex = modal_value(modal, "prior_proposal_root");
    let vote = modal_value(modal, "vote").to_ascii_lowercase();
    if let Err(embed) = hosted_user_cell(modal.user.id.get(), state).await {
        return embed;
    }
    let namespace_cell = match parse_cell_id(&namespace_cell_hex) {
        Ok(cell) => cell,
        Err(embed) => return embed,
    };
    let prior_proposal_root = match parse_field_hex(&prior_proposal_root_hex) {
        Ok(root) => root,
        Err(embed) => return embed,
    };
    let vote_kind = match vote.as_str() {
        "yes" => VoteKind::Approve,
        "no" => VoteKind::Reject,
        _ => return embeds::error_embed("Invalid Vote", "Vote must be `yes` or `no`."),
    };
    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        modal.user.id.get(),
        state.federation_id_bytes,
    );
    let action = build_vote_on_proposal_action(
        &cclerk.app,
        namespace_cell,
        prior_proposal_root,
        vote_kind,
        1,
    );
    match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:governance:vote:{vote}:guild:{guild_id}")),
        )
        .await
    {
        Ok(result) if result.accepted => embeds::success_embed("Vote Submitted")
            .field("Namespace", short_cell(&namespace_cell_hex), true)
            .field("Vote", vote, true)
            .field("Prior Proposal Root", short_cell(&prior_proposal_root_hex), false)
            .field("Turn", turn_hash_field(result.turn_hash), false),
        Ok(result) => embeds::error_embed(
            "Vote Rejected",
            result
                .error
                .as_deref()
                .unwrap_or("node rejected the signed governance action"),
        ),
        Err(e) => embeds::error_embed("Node Unreachable", &e.to_string()),
    }
}

async fn submit_subscription_create(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let Some(guild_id) = modal.guild_id.map(|id| id.get()) else {
        return embeds::warning_embed("Guild Required", "Queues must be created in a server.");
    };
    let name = modal_value(modal, "name");
    let rate_limit = match parse_optional_i64(&modal_value(modal, "rate_limit"), "Rate Limit") {
        Ok(value) => value,
        Err(embed) => return embed,
    };
    let deposit = match parse_optional_i64(&modal_value(modal, "deposit"), "Minimum Deposit") {
        Ok(value) => value,
        Err(embed) => return embed,
    };
    let namespace_path = format!("/discord/{guild_id}/{name}");
    let capacity = rate_limit.unwrap_or(1024).max(1) as u64;
    let body = serde_json::json!({
        "capacity": capacity,
        "program_vk": serde_json::Value::Null,
    });

    let url = format!("{}/queues/allocate", state.config.devnet_url);
    match state.devnet.client().post(&url).json(&body).send().await {
        Ok(resp) if resp.status().is_success() => {
            let allocated: QueueAllocateResponse = match resp.json().await {
                Ok(value) => value,
                Err(e) => return embeds::error_embed("Parse Error", &e.to_string()),
            };
            let actor = modal.user.id.get().to_string();
            if let Err(e) = state
                .db
                .upsert_starbridge_queue(
                    &namespace_path,
                    &guild_id.to_string(),
                    &name,
                    &allocated.queue_id,
                    &actor,
                    None,
                    rate_limit,
                    deposit,
                )
                .await
            {
                return embeds::error_embed("Queue State Error", &e.to_string());
            }
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.allocate",
                    &actor,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    "accepted",
                    serde_json::json!({
                        "queue_id": &allocated.queue_id,
                        "capacity": capacity,
                    }),
                )
                .await;

            embeds::success_embed("Queue Created")
                .field("Name", name, true)
                .field("Path", format!("`{namespace_path}`"), true)
                .field("Queue ID", short_queue(&allocated.queue_id), true)
                .field(
                    "Rate Limit",
                    rate_limit.map_or("none".to_string(), |r| format!("{r}/min")),
                    true,
                )
                .field(
                    "Min Deposit",
                    deposit.map_or("none".to_string(), |d| format!("{d} computrons")),
                    true,
                )
        }
        Ok(resp) => embeds::error_embed("Queue Creation Failed", &response_text(resp).await),
        Err(e) => embeds::error_embed("Node Unreachable", &e.to_string()),
    }
}

async fn submit_subscription_publish(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let Some(guild_id) = modal.guild_id.map(|id| id.get()) else {
        return embeds::warning_embed(
            "Guild Required",
            "Queue publishing must happen in a server.",
        );
    };
    let name = modal_value(modal, "name");
    let message = modal_value(modal, "message");
    let namespace_path = format!("/discord/{guild_id}/{name}");
    let queue = match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(queue)) => queue,
        Ok(None) => {
            return embeds::warning_embed(
                "Queue Not Found",
                &format!("No queue is mounted at `{namespace_path}`. Create it first."),
            );
        }
        Err(e) => return embeds::error_embed("Queue State Error", &e.to_string()),
    };
    let message_hash = message_hash_hex(&message);
    let body = serde_json::json!({
        "message_hash": &message_hash,
        "deposit": 0,
    });

    let url = format!(
        "{}/queues/{}/enqueue",
        state.config.devnet_url, queue.queue_id
    );
    match state.devnet.client().post(&url).json(&body).send().await {
        Ok(resp) if resp.status().is_success() => {
            let result: QueueEnqueueResponse = resp
                .json()
                .await
                .unwrap_or(QueueEnqueueResponse { position: 0 });
            let actor = modal.user.id.get().to_string();
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.enqueue",
                    &actor,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    "accepted",
                    serde_json::json!({
                        "queue_id": &queue.queue_id,
                        "position": result.position,
                        "message_hash": &message_hash,
                    }),
                )
                .await;

            embeds::success_embed("Published")
                .field("Queue", name, true)
                .field("Position", result.position.to_string(), true)
                .field("Message", format!("`{}`", truncate(&message, 100)), false)
        }
        Ok(resp) => embeds::error_embed("Publish Failed", &response_text(resp).await),
        Err(e) => embeds::error_embed("Node Unreachable", &e.to_string()),
    }
}

async fn submit_subscription_subscribe(modal: &ModalInteraction, state: &BotState) -> CreateEmbed {
    let Some(guild_id) = modal.guild_id.map(|id| id.get()) else {
        return embeds::warning_embed(
            "Guild Required",
            "Queue subscriptions must happen in a server.",
        );
    };
    let name = modal_value(modal, "name");
    let namespace_path = format!("/discord/{guild_id}/{name}");
    match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(_)) => {}
        Ok(None) => {
            return embeds::warning_embed(
                "Queue Not Found",
                &format!("No queue is mounted at `{namespace_path}`. Create it first."),
            );
        }
        Err(e) => return embeds::error_embed("Queue State Error", &e.to_string()),
    }

    let discord_id = modal.user.id.get().to_string();
    match state
        .db
        .subscribe_starbridge_queue(&namespace_path, &discord_id)
        .await
    {
        Ok(inserted) => {
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.subscribe",
                    &discord_id,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    if inserted { "accepted" } else { "unchanged" },
                    serde_json::json!({}),
                )
                .await;
            embeds::success_embed(if inserted {
                "Subscribed"
            } else {
                "Already Subscribed"
            })
            .description(format!(
                "You will receive DMs when new messages arrive in **{name}**."
            ))
            .field("Queue", name, true)
            .field("Path", format!("`{namespace_path}`"), true)
        }
        Err(e) => embeds::error_embed("Subscribe Failed", &e.to_string()),
    }
}

async fn user_cell(user_id: u64, state: &BotState) -> Result<String, CreateEmbed> {
    match state.db.get_user_identity(&user_id.to_string()).await {
        Ok(Some(identity)) if identity.mode != IdentityMode::ExternalPending => {
            Ok(identity.cell_id)
        }
        Ok(Some(_)) => Err(embeds::warning_embed(
            "Identity Pending",
            "Your external identity link is pending ownership proof.",
        )),
        Ok(None) => Err(embeds::warning_embed(
            "No Cipherclerk",
            "Create a hosted cipherclerk with `/cipherclerk create` first.",
        )),
        Err(e) => Err(embeds::error_embed("Database Error", &e.to_string())),
    }
}

async fn hosted_user_cell(user_id: u64, state: &BotState) -> Result<String, CreateEmbed> {
    match state.db.get_user_identity(&user_id.to_string()).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => Ok(identity.cell_id),
        Ok(Some(_)) => Err(embeds::warning_embed(
            "Hosted Identity Required",
            "This bot can only sign this action for a hosted `/cipherclerk create` identity.",
        )),
        Ok(None) => Err(embeds::warning_embed(
            "No Cipherclerk",
            "Create a hosted cipherclerk with `/cipherclerk create` first.",
        )),
        Err(e) => Err(embeds::error_embed("Database Error", &e.to_string())),
    }
}

#[derive(serde::Deserialize)]
struct QueueAllocateResponse {
    #[serde(rename = "queueId")]
    queue_id: String,
}

#[derive(serde::Deserialize)]
struct QueueEnqueueResponse {
    position: u64,
}

async fn response_text(resp: reqwest::Response) -> String {
    let status = resp.status();
    let body = resp.text().await.unwrap_or_default();
    if body.is_empty() {
        status.to_string()
    } else {
        truncate(&body, 900)
    }
}

fn parse_optional_i64(value: &str, label: &str) -> Result<Option<i64>, CreateEmbed> {
    if value.trim().is_empty() {
        Ok(None)
    } else {
        value.trim().parse::<i64>().map(Some).map_err(|_| {
            embeds::warning_embed(
                &format!("Invalid {label}"),
                &format!("{label} must be an integer."),
            )
        })
    }
}

fn modal_value(modal: &ModalInteraction, id: &str) -> String {
    for row in &modal.data.components {
        for component in &row.components {
            if let ActionRowComponent::InputText(input) = component {
                if input.custom_id == id {
                    return input.value.clone().unwrap_or_default().trim().to_string();
                }
            }
        }
    }
    String::new()
}

fn code_field(value: Option<&serde_json::Value>) -> String {
    let text = value_to_string(value);
    if text.is_empty() {
        "`unavailable`".to_string()
    } else {
        format!("`{}`", truncate(&text, 120))
    }
}

fn code_block(value: Option<&serde_json::Value>) -> String {
    let text = value_to_string(value);
    if text.is_empty() {
        "```unavailable```".to_string()
    } else {
        format!("```\n{}\n```", truncate(&text, 1500))
    }
}

fn value_to_string(value: Option<&serde_json::Value>) -> String {
    match value {
        Some(serde_json::Value::String(s)) => s.clone(),
        Some(value) if !value.is_null() => value.to_string(),
        _ => String::new(),
    }
}

fn parse_cell_id(value: &str) -> Result<CellId, CreateEmbed> {
    parse_cell_bytes(value).map(CellId)
}

fn parse_field_hex(value: &str) -> Result<FieldElement, CreateEmbed> {
    parse_cell_bytes(value)
}

fn parse_cell_bytes(value: &str) -> Result<[u8; 32], CreateEmbed> {
    let trimmed = value
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| value.trim());
    let bytes = hex::decode(trimmed).map_err(|_| {
        embeds::warning_embed(
            "Invalid Cell",
            "Cell IDs must be 64 lowercase hex characters.",
        )
    })?;
    bytes.try_into().map_err(|_| {
        embeds::warning_embed("Invalid Cell", "Cell IDs must decode to exactly 32 bytes.")
    })
}

#[derive(serde::Deserialize)]
struct RouteSpec {
    path: String,
    target: serde_json::Value,
}

fn parse_route_table(value: &str) -> Result<RouteTable, CreateEmbed> {
    let specs: Vec<RouteSpec> = serde_json::from_str(value).map_err(|e| {
        embeds::warning_embed(
            "Invalid Routes JSON",
            &format!("Expected an array of routes: {e}"),
        )
    })?;
    if specs.is_empty() {
        return Err(embeds::warning_embed(
            "Invalid Routes JSON",
            "At least one route is required.",
        ));
    }

    let mut owned = Vec::with_capacity(specs.len());
    for spec in specs {
        if spec.path.trim().is_empty() {
            return Err(embeds::warning_embed(
                "Invalid Routes JSON",
                "Route paths cannot be empty.",
            ));
        }
        owned.push((spec.path, parse_route_target(&spec.target)?));
    }
    let borrowed: Vec<(&str, RouteTarget)> = owned
        .iter()
        .map(|(path, target)| (path.as_str(), target.clone()))
        .collect();
    Ok(build_route_table(&borrowed))
}

fn parse_route_target(value: &serde_json::Value) -> Result<RouteTarget, CreateEmbed> {
    if let Some(name) = value.as_str() {
        return Ok(if name == "drop" {
            RouteTarget::drop()
        } else {
            RouteTarget::handler(name)
        });
    }

    let obj = value.as_object().ok_or_else(|| {
        embeds::warning_embed(
            "Invalid Routes JSON",
            "Route target must be a string or object.",
        )
    })?;
    if obj.get("drop").and_then(|v| v.as_bool()) == Some(true) {
        return Ok(RouteTarget::drop());
    }
    if let Some(handler) = obj.get("handler").and_then(|v| v.as_str()) {
        return Ok(RouteTarget::handler(handler));
    }
    if let Some(federation) = obj.get("federation").and_then(|v| v.as_str()) {
        return parse_cell_bytes(federation).map(RouteTarget::federation);
    }
    match obj.get("type").and_then(|v| v.as_str()) {
        Some("drop") => Ok(RouteTarget::drop()),
        Some("handler") => obj
            .get("value")
            .and_then(|v| v.as_str())
            .map(RouteTarget::handler)
            .ok_or_else(|| embeds::warning_embed("Invalid Routes JSON", "Handler targets need a string `value`.")),
        Some("federation") => obj
            .get("value")
            .and_then(|v| v.as_str())
            .ok_or_else(|| embeds::warning_embed("Invalid Routes JSON", "Federation targets need a hex `value`."))
            .and_then(|hex| parse_cell_bytes(hex).map(RouteTarget::federation)),
        _ => Err(embeds::warning_embed(
            "Invalid Routes JSON",
            "Target object must contain `handler`, `federation`, `drop`, or a supported `type`.",
        )),
    }
}

fn short_cell(cell: &str) -> String {
    format!("`{}...`", &cell[..16.min(cell.len())])
}

fn short_queue(queue_id: &str) -> String {
    format!("`{}...`", &queue_id[..16.min(queue_id.len())])
}

fn message_hash_hex(message: &str) -> String {
    hex::encode(blake3::hash(message.as_bytes()).as_bytes())
}

fn turn_hash_field(hash: Option<String>) -> String {
    hash.map(|hash| format!("`{hash}`"))
        .unwrap_or_else(|| "`unknown`".to_string())
}

fn truncate(value: &str, max: usize) -> String {
    if value.chars().count() <= max {
        value.to_string()
    } else {
        let mut out = value
            .chars()
            .take(max.saturating_sub(1))
            .collect::<String>();
        out.push_str("...");
        out
    }
}
