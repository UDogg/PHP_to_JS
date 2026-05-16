<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::create('login_api_tokens', function (Blueprint $table) {
            $table->id();
            $table->string('user_name', 100);
            $table->uuid('access_token')->unique();
            $table->enum('status', ['Y', 'N'])->default('Y');
            $table->timestamp('expires_at')->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('login_api_tokens');
    }
};
