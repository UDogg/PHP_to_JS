<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    public function up(): void
    {
        Schema::table('journey_api_token', function (Blueprint $table) {
            $table->longText('encrypted_form_data')->nullable()->change();
        });
    }

    public function down(): void
    {
        Schema::table('journey_api_token', function (Blueprint $table) {
            $table->string('encrypted_form_data')->nullable()->change();
        });
    }
};
