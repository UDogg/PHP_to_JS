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
        if (!Schema::hasTable('config_settings')) {
            Schema::create('config_settings', function (Blueprint $table) {
                $table->increments('credential_id');
                $table->string('credential_label',50);
                $table->string('credential_key',50);
                $table->string('credential_value',255);
                $table->string('enviroment',);
                $table->timestamps();
                $table->softDeletes();
            });
        }
        
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('config_settings');
    }
};
