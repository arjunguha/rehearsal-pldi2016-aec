@model $rootnamespace$.Models.IAlert

<div class="alert alert-@Model.NotificationType">
    @Model.Message
</div>
